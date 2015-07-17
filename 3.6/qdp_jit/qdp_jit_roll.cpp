//===- LoadCombine.cpp - Combine Adjacent Loads ---------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
/// \file
/// This transformation combines adjacent loads.
///
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Scalar.h"

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/Statistic.h"
//#include "llvm/Analysis/AliasAnalysis.h"
//#include "llvm/Analysis/AliasSetTracker.h"
#include "llvm/Analysis/TargetFolder.h"
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/ADT/SetVector.h"
#include <queue>
#include <vector>
#include <sstream>
#include <algorithm>

using namespace llvm;

#define SV_NAME "qdp_jit_roll0"
#define DEBUG_TYPE SV_NAME

//STATISTIC(NumLoadsAnalyzed, "Number of loads analyzed for combining");
//STATISTIC(NumLoadsCombined, "Number of loads combined");

namespace {


class qdp_jit_roll : public ModulePass {
public:
  const char *getPassName() const override { return "qdp_jit_roll"; }
  static char ID;

  qdp_jit_roll()
      : ModulePass(ID),
        C(nullptr), DL(nullptr) {
    //initializeSROAPass(*PassRegistry::getPassRegistry());
  }
  
  //  using llvm::Pass::doInitialization;
  //bool doInitialization(Function &) override;
  //bool runOnFunction(Function &F) override;
  bool runOnModule(Module &M) override;

protected:
  struct reduction {
    SetVector<Value*> instructions;
    std::vector< std::vector<uint64_t> > offsets;  // outer: iteration, inner: GEP instruction within iteration
    int id;
  };
  typedef std::vector<reduction> reductions_t;

  void add_GEPs(BasicBlock &BB);
  void collectRoots( Instruction& I, SetVector<Value*>& all_roots);
  void collectAllUses( SetVector<Value*>& to_visit, SetVector<Value*>& all_uses);
  //  void collectAll( Instruction& I);
  void collectForStoresAllOperandsAll( SetVector<Value*>& tree );
  void collectAllInstructionOperands( SetVector<Value*>& roots, SetVector<Value*>& operands );
  bool track( SetVector<Value*>& set);
  void modify_loop_body( reduction& red , Value* ind_var , int64_t offset_normalize );
  //bool insert_loop( reductions_t::iterator cur , Function* F, BasicBlock* successor);
  BasicBlock* insert_loop( reductions_t::iterator cur , Function* F, BasicBlock* insert_before,BasicBlock* take_instr_from);
  //void getAnalysisUsage(AnalysisUsage &AU) const override;



private:
  reductions_t reductions;
  Function* function;

  Module* module;
  typedef IRBuilder<true, TargetFolder> BuilderTy;
  LLVMContext *C;
  const DataLayout *DL;
  //  AliasAnalysis *AA;

  BuilderTy *Builder;
};
}





void qdp_jit_roll::collectRoots( Instruction& I, SetVector<Value*>& all_roots) {
  //DEBUG(dbgs() << "collectRoots for " << I << "\n");

  all_roots.clear();
  std::queue<Value*> to_visit;

  to_visit.push(&I);

  while (!to_visit.empty()) {
    Value* v = to_visit.front();
    to_visit.pop();
    Instruction* vi;
    if ((vi = dyn_cast<Instruction>(v))) {
      for (Use& U : vi->operands()) {
	if (isa<Instruction>(U.get())) {
	  to_visit.push(U.get());
	} else {
	  if (!isa<Constant>(U.get())) {
	    //DEBUG(dbgs() << "An operand is a non-instruction " << *U.get() << "  root=" << *v << "\n");
	    all_roots.insert(v);
	  }
	}
      }
    }
  }
}



void qdp_jit_roll::collectAllInstructionOperands( SetVector<Value*>& roots, SetVector<Value*>& operands ) {
  while (!roots.empty()) {
    Value* v = roots.back();
    roots.pop_back();
    if (Instruction * vi = dyn_cast<Instruction>(v)) {
      //DEBUG(dbgs() << "Found instruction " << *vi << "\n");
      operands.insert(v);
      for (Use& U : vi->operands()) {
	roots.insert(U.get());
      }
    }
  }
}



void qdp_jit_roll::collectForStoresAllOperandsAll( SetVector<Value*>& tree ) {
  //DEBUG(dbgs() << "size of tree a) " << tree.size() << "\n");

  SetVector<Value*> add_to;
  
  for (Value *v : tree ) {
    if (isa<StoreInst>(*v)) {
      //DEBUG(dbgs() << "store " << *v << "\n");
      User* user = cast<User>(v);
      add_to.insert( user->getOperand(1) ); // only the pointer
    }
  }


  collectAllInstructionOperands(add_to,tree);
  
	//DEBUG(dbgs() << "operand " << *U.get() << "\n");
	// if (isa<Instruction>(U.get())) {
	//   DEBUG(dbgs() << "inserting " << *U.get() << "\n");
	//   tree.insert(U.get());
	// }
      
  //DEBUG(dbgs() << "size of tree b) " << tree.size() << "\n");
}


void qdp_jit_roll::collectAllUses( SetVector<Value*>& to_visit, SetVector<Value*>& all_uses) {
  //DEBUG(dbgs() << "collectAllUses " << "\n");

  all_uses.clear();

  while (!to_visit.empty()) {
    Value* v = to_visit.back();
    //DEBUG(dbgs() << "to_visit size " << to_visit.size() << " visiting " << *v << "\n");
    all_uses.insert(v);
    to_visit.pop_back();

    //DEBUG(dbgs() << "getNumUses " << v->getNumUses() << "\n");
    for (Use &U : v->uses()) {
      //DEBUG(dbgs() << "user " << *U.getUser() << "\n");
      to_visit.insert(U.getUser());
    }

  }
}


void qdp_jit_roll::add_GEPs(BasicBlock &BB) {
  for (Instruction& I : BB) {
    if (BitCastInst* BCI = dyn_cast<BitCastInst>(&I)) {
      //DEBUG(dbgs() << "Found BitCastInst " << BCI << "\n");
      
      for (Use& U : I.operands()) {
      	Value* V = U.get();
      	if (!dyn_cast<Instruction>(V)) {
      	  //DEBUG(dbgs() << "Found argument " << *V << "\n");
	  std::vector<llvm::Value*> vect_1;
	  vect_1.push_back(Builder->getInt64(0));

	  llvm::GetElementPtrInst* gep1 = llvm::GetElementPtrInst::Create( V , ArrayRef< Value * >(vect_1) );

	  BB.getInstList().insert(&I, gep1);

	  BCI->setOperand( 0 , gep1 );
      	}
      }
    }
    if (LoadInst* LI = dyn_cast<LoadInst>(&I)) {
      //DEBUG(dbgs() << "Found LoadInst " << LI << "\n");
      
      for (Use& U : I.operands()) {
      	Value* V = U.get();
      	if (!dyn_cast<Instruction>(V)) {
      	  //DEBUG(dbgs() << "Found argument " << *V << "\n");
	  std::vector<llvm::Value*> vect_1;
	  vect_1.push_back(Builder->getInt64(0));

	  llvm::GetElementPtrInst* gep1 = llvm::GetElementPtrInst::Create( V , ArrayRef< Value * >(vect_1) );

	  BB.getInstList().insert(&I, gep1);

	  LI->setOperand( 0 , gep1 );
      	}
      }
    }
  }
}



bool qdp_jit_roll::track( SetVector<Value*>& set) {
  DEBUG(dbgs() << "Track set with " << set.size() << " instructions.\n");

  static int id;

  // if (reductions.empty()) {
  //   reductions.push_back( reduction() );
  //   reductions[0].instructions.insert( set.begin() , set.end() );
  //   reductions[0].offsets.push_back(0);
  //   reductions[0].id = id++;
  //   return false;
  // }

  bool reduction_found = false;

  reductions_t::iterator cur_reduction;

  for ( cur_reduction = reductions.begin();
	cur_reduction != reductions.end() && !reduction_found ; 
	++cur_reduction ) {

    DEBUG(dbgs() << "Trying reduction " << cur_reduction->id << "\n");


    //DEBUG(dbgs() << "current reduction: " << "\n");
    SetVector<Value*> reduction_stores;
    for (Value *v : cur_reduction->instructions ) {
      //DEBUG(dbgs() << *v << "\n");
      if (isa<StoreInst>(*v)) {
	reduction_stores.insert(v);
      }
    }
    //DEBUG(dbgs() << "incoming set: " << "\n");
    SetVector<Value*> set_stores;
    for (Value *v : set ) {
      //DEBUG(dbgs() << *v << "\n");
      if (isa<StoreInst>(*v)) {
	set_stores.insert(v);
      }
    }


    if (cur_reduction->instructions.size() != set.size()) {
      DEBUG(dbgs() << " -> number of instructions not identical, " << cur_reduction->instructions.size() << " " << set.size() << "\n");
      continue;
    }

    if (reduction_stores.size() != set_stores.size()) {
      DEBUG(dbgs() << " -> number of stores not identical, " << reduction_stores.size() << " " << set_stores.size() << "\n");
      continue;
    }

    bool mismatch = false;

    for (uint64_t i = 0 ; i < set_stores.size() && !mismatch; ++i ) {

      SetVector<Value*> cmp0_visit;
      SetVector<Value*> cmp1_visit;
      cmp0_visit.insert( set_stores[0] );
      cmp1_visit.insert( reduction_stores[0] );

      while ( !cmp0_visit.empty() && !cmp1_visit.empty() && !mismatch ) {
	Value* v0 = cmp0_visit.back();
	Value* v1 = cmp1_visit.back();
	cmp0_visit.pop_back();
	cmp1_visit.pop_back();
	if (Instruction * vi0 = dyn_cast<Instruction>(v0)) {
	  if (Instruction * vi1 = dyn_cast<Instruction>(v1)) {
	    if ( vi0->getOpcode() == vi1->getOpcode() ) {
	      //DEBUG(dbgs() << "found matching instructions " << *vi0 << " " << *vi1 << "\n");
	    
	      for (Use& U0 : vi0->operands()) {
		cmp0_visit.insert(U0.get());
	      }
	      for (Use& U1 : vi1->operands()) {
		cmp1_visit.insert(U1.get());
	      }
	      if (cmp0_visit.size() != cmp1_visit.size()) {
		DEBUG(dbgs() << "found mismatching number of operands " << cmp0_visit.size() << " " << cmp1_visit.size() << "\n");
		mismatch=true;
	      }
	    } else {
	      DEBUG(dbgs() << "found mismatching opcode" << *vi0 << " " << *vi1 << "\n");
	      mismatch=true;
	    }
	  } else {
	    mismatch=true;
	    // v1 is not an instruction
	  }
	}
      }
    }

    if (!mismatch) {
      reduction_found = true;
      break;
    }
  }

  // Scan linearily through the current set and collect GEP's offsets

  
  //SetVector<GetElementPtrInst*> GEPs_in_set;
  std::vector<uint64_t> GEP_offsets;

  DEBUG(dbgs() << "GEP offsets: ");
  for (Value* I : set) {
    if (Instruction * gep0 = dyn_cast<GetElementPtrInst>(I)) {
      if (ConstantInt * ci0 = dyn_cast<ConstantInt>(gep0->getOperand(1))) {
	GEP_offsets.push_back( ci0->getZExtValue() );
	DEBUG(dbgs() << ci0->getZExtValue() << " ");
      }
    }
  }
  DEBUG(dbgs() << "\n");

  if (reduction_found) {
    DEBUG(dbgs() << "Match with reduction id = " << cur_reduction->id << "\n");
    cur_reduction->offsets.push_back( GEP_offsets );
    return true;
  }

  DEBUG(dbgs() << "No existing reduction matches, will add another reduction, with id = " << id << "\n");
  reductions.push_back( reduction() );
  reductions.back().instructions.insert( set.begin() , set.end() );
  reductions.back().offsets.push_back( GEP_offsets );
  reductions.back().id = id++;
  return false;
}







//
// returns the block (loop start) that was inserted
//
BasicBlock* qdp_jit_roll::insert_loop( reductions_t::iterator cur , Function* F, BasicBlock* insert_before,BasicBlock* take_instr_from)
{
  DEBUG(dbgs() << "Insert loop called with reduction number " << cur->id << "\n");

  if (cur->offsets.size() < 2) {
    DEBUG(dbgs() << "This reduction has only 1 iteration, we won't roll this.\n");
    return insert_before;
  }

  size_t gep_total_number = cur->offsets[0].size();
  DEBUG(dbgs() << "gep_total_number = " << gep_total_number << ".\n");

  std::vector<bool> gep_cont(gep_total_number);
  std::vector<uint64_t> gep_lo(gep_total_number);
  std::vector<uint64_t> gep_hi(gep_total_number);
  std::vector<uint64_t> gep_step(gep_total_number);
  std::vector<int64_t> gep_ref_delta(gep_total_number);
  bool use_global_array=false;
  uint64_t loop_count = cur->offsets.size();

  //
  // First we assume that all GEPs are contiguous
  //
  for ( size_t gep_num = 0 ; gep_num < gep_total_number ; ++gep_num ) {
    gep_lo[ gep_num ]   = cur->offsets[0][gep_num];
    gep_hi[ gep_num ]   = cur->offsets[1][gep_num];
    gep_step[ gep_num ] = gep_hi[ gep_num ] - gep_lo[ gep_num ];
    gep_cont[ gep_num ] = true;
  }


  for ( size_t it_num = 2 ; it_num < cur->offsets.size() ; ++it_num ) {
    for ( size_t gep_num = 0 ; gep_num < gep_total_number ; ++gep_num ) {
      if ( gep_cont[ gep_num ] ) {
	uint64_t off = cur->offsets[it_num][gep_num];
	if ( gep_hi[gep_num] + gep_step[gep_num] == off ) {
	  gep_hi[gep_num] = off;
	} else {
	  gep_cont[gep_num] = false;
	  use_global_array = true;
	}
      }
    }
  }


  for ( size_t gep_num = 0 ; gep_num < gep_total_number ; ++gep_num ) {
    if ( !gep_cont[ gep_num ] ) {
      gep_ref_delta[ gep_num ] = cur->offsets[0][gep_num];
    }
  }

  std::vector< uint64_t > deltas;
  deltas.push_back(0); // The first iteration has always a delta equal to zero
  bool loop_roll_not_possible = false;

  for ( size_t it_num = 1 ; it_num < cur->offsets.size() ; ++it_num ) {
    bool delta_set = false;
    int64_t delta;
    for ( size_t gep_num = 0 ; gep_num < gep_total_number ; ++gep_num ) {
      if ( !gep_cont[ gep_num ] ) {
	if (!delta_set) {
	  delta_set = true;
	  delta = cur->offsets[it_num][gep_num] - gep_ref_delta[gep_num];
	  if (delta < 0) {
	    DEBUG(dbgs() << "WARNING: negative delta, " << delta << " !\n");
	  }
	  deltas.push_back( (uint64_t)delta );
	} else {
	  if (delta != (int64_t)(cur->offsets[it_num][gep_num]) - gep_ref_delta[gep_num]) {
	    // This GEP deviates
	    DEBUG(dbgs() << "GEP number " << gep_num << " cannot be rolled into a loop!\n");
	    loop_roll_not_possible = true;
	  }
	}
      }
    }
  }


  if (!loop_roll_not_possible) {
    for ( size_t gep_num = 0 ; gep_num < gep_total_number ; ++gep_num ) {
      DEBUG(dbgs() << "gep " << gep_num << " : ");
      if (gep_cont[gep_num]) {
	DEBUG(dbgs() << "lo = " << gep_lo[gep_num] << "  ");
	DEBUG(dbgs() << "hi = " << gep_hi[gep_num] << "  ");
	DEBUG(dbgs() << "step = " << gep_step[gep_num] << "\n");
      } else {
	DEBUG(dbgs() << "not contiguous, use delta ref " << gep_ref_delta[gep_num] << "\n");
      }
    }
    for (int64_t delta: deltas) {
      DEBUG(dbgs() << delta << " ");
    }
    DEBUG(dbgs() << "\n");
  } else {
    DEBUG(dbgs() << "Loop roll not possible\n");
  }


  GlobalVariable* offset_var;
  if (use_global_array) {
    Constant* CDA = ConstantDataArray::get( llvm::getGlobalContext() , 
					    ArrayRef<uint64_t>( deltas.data() , deltas.size() ) );
    ArrayType *array_type = ArrayType::get( Type::getIntNTy(getGlobalContext(),64) , deltas.size() );
    
    offset_var = new GlobalVariable(*module, array_type , true, GlobalValue::InternalLinkage, CDA , "offset_array" );
  }


  llvm::BasicBlock *BBe = llvm::BasicBlock::Create(llvm::getGlobalContext(), "exit_loop" );
  F->getBasicBlockList().push_front(BBe);

  llvm::BasicBlock *BBl = llvm::BasicBlock::Create(llvm::getGlobalContext(), "loop" );
  F->getBasicBlockList().push_front(BBl);

  llvm::BasicBlock *BB0 = llvm::BasicBlock::Create(llvm::getGlobalContext(), "pre_loop" );
  F->getBasicBlockList().push_front(BB0);

  Builder->SetInsertPoint(BBe);
  Builder->CreateBr(insert_before);

  Builder->SetInsertPoint(BB0);
  Builder->CreateBr(BBl);

  //Builder->SetInsertPoint(&BB,BB.begin());
  Builder->SetInsertPoint(BBl);
  PHINode * PN = Builder->CreatePHI( Type::getIntNTy(getGlobalContext(),64) , 2 );
  
  Value *cond;
  Value *PNp1;

  PNp1 = Builder->CreateNSWAdd( PN , ConstantInt::get( Type::getIntNTy(getGlobalContext(),64) , 1 ) );
  cond = Builder->CreateICmpUGT( PNp1 , ConstantInt::get( Type::getIntNTy(getGlobalContext(),64) , loop_count ) );
  PN->addIncoming( ConstantInt::get( Type::getIntNTy(getGlobalContext(),64) , 0 ) , BB0 );
  PN->addIncoming( PNp1 , BBl );

  Builder->CreateCondBr( cond , BBe, BBl);


  BasicBlock::iterator inst_search_start = take_instr_from->begin();
  while(1) {
    BasicBlock::iterator inst_set_begin;
    bool notfound = true;
    for (inst_set_begin = inst_search_start ; inst_set_begin != take_instr_from->end() ; ++inst_set_begin ) {
      if (cur->instructions.count(inst_set_begin)) {
	notfound = false;
	break;
      }
    }
    if (notfound) {
      // we could be in a stream after a few hits
      break;
    }
    BasicBlock::iterator inst_set_end;
    for (inst_set_end = inst_set_begin ; inst_set_end != take_instr_from->end() ; ++inst_set_end ) {
      if (!cur->instructions.count(inst_set_end)) {
	break;
      }
    }
    //successor->dump();
    DEBUG(dbgs() << "Using the following enclosing instructions\n" );    
    DEBUG(dbgs() << *inst_set_begin << "\n" );
    DEBUG(dbgs() << *inst_set_end << "\n" );

    BBl->getInstList().splice( cast<Instruction>(PNp1) , take_instr_from->getInstList() , inst_set_begin , inst_set_end );
    inst_search_start = inst_set_end;
  }


  int gep_num = 0;
  bool offset_loaded = false;
  Value* offset_read;

  for( Value* V : cur->instructions ) {
    if (GetElementPtrInst * gep0 = dyn_cast<GetElementPtrInst>(V)) {
      Builder->SetInsertPoint(gep0);
      if (gep_cont[gep_num]) {
	Value *new_gep_address = Builder->CreateMul( PN , ConstantInt::get( Type::getIntNTy(getGlobalContext(),64) , 
									    gep_step[gep_num] ) );
	if (gep_lo[gep_num]) {
	  new_gep_address = Builder->CreateAdd( new_gep_address, ConstantInt::get( Type::getIntNTy(getGlobalContext(),64) , 
										   gep_lo[gep_num] ) );
	}

	gep0->setOperand( 1 , new_gep_address );
      } else {
	if (!offset_loaded) {
	  std::vector<Value*> tmp;
	  tmp.push_back( ConstantInt::get( Type::getIntNTy(getGlobalContext(),64) , 0 ) );
	  tmp.push_back( PN );
	  Builder->SetInsertPoint( PN->getNextNode() );
	  Value* offset_GEP = Builder->CreateGEP( offset_var , ArrayRef<Value*>(tmp) );
	  offset_read = Builder->CreateLoad( offset_GEP );
	  offset_loaded = true;
	  Builder->SetInsertPoint(gep0);
	}
	Value *new_gep_address = offset_read;
	if (gep_ref_delta[gep_num]) {
	  new_gep_address = Builder->CreateAdd( new_gep_address, ConstantInt::get( Type::getIntNTy(getGlobalContext(),64) , 
										   gep_ref_delta[gep_num] ) );
	}
	gep0->setOperand( 1 , new_gep_address );
      }
      gep_num++;
    }
  }

  //function->dump();

  return insert_before;
}




bool qdp_jit_roll::runOnModule(Module &M) {
  module = &M;
  IRBuilder<true, TargetFolder> TheBuilder(M.getContext(), TargetFolder(DL));
  Builder = &TheBuilder;

  Function* F_ptr = NULL;
  for( Module::iterator MI = M.begin(), ME = M.end();
       MI != ME; ++MI ) {
    if (Function* F0 = dyn_cast<Function>(MI)) {
      if (F0->getName() == "main") {
	F_ptr = MI;
      }
    }
  }
  if (!F_ptr) {
    DEBUG(dbgs() << "No function with name 'main' found. Giving up."  << "\n");
    return false;
  }

  Function& F = *F_ptr;
  function=&F;
  
#if 1
  DEBUG(dbgs() << "Running on F"  << "\n");

  BasicBlock& BB = F.getEntryBlock();

  add_GEPs(BB);

  SetVector<Value*> all_roots;
  SetVector<Value*> processed;
  SetVector<Value*> for_erasure;

#ifndef NDEBUG	
  bool first_set = true;
#endif
  int marked_erasure = 0;
  for (Instruction& I : BB) {
    if (isa<StoreInst>(I)) {
      if (processed.count( &I ) == 0 ) {

#ifndef NDEBUG
	std::stringstream ss;
	std::string str;
	llvm::raw_string_ostream rso(str);
#endif
	DEBUG(rso << "Found new StoreInst ");
	DEBUG(I.print(rso));
	DEBUG(rso << "\n");

	collectRoots(I, all_roots);
	DEBUG(rso << "Root instructions                        = " << all_roots.size() << "\n");

	SetVector<Value*> all_uses;
	collectAllUses(all_roots,all_uses);      
	DEBUG(rso << "Uses (of the roots)                      = " << all_uses.size() << "\n");

	collectForStoresAllOperandsAll(all_uses);
	DEBUG(rso << "Uses (incl. from other reachable stores) = " << all_uses.size() << "\n");


	if (track(all_uses)) {
	  for_erasure.insert( all_uses.begin(), all_uses.end() );
	  marked_erasure++;
	  //DEBUG(dbgs() << "Marked for erasure!" << "\n");
	}

#ifndef NDEBUG	
	if (first_set)
	  dbgs() << rso.str();
	first_set=false;
#endif

	processed.insert(all_uses.begin(),all_uses.end());

      } else {
	//DEBUG(dbgs() << "Found already processed StoreInst " << I << "\n");
      }
    }
  }

  DEBUG(dbgs() << "Total instructions processed        = " << processed.size() << "\n");
  DEBUG(dbgs() << "Instruction sets marked for erasure = " << marked_erasure << "\n");


  DEBUG(dbgs() << "Erasing instruction count = " << for_erasure.size() << "\n");
  for ( Value* v: for_erasure ) {
    if (Instruction *Inst = dyn_cast<Instruction>(v)) {
      //DEBUG(dbgs() << "erasure: " << *Inst << "\n");
      if (!Inst->use_empty())
	Inst->replaceAllUsesWith(UndefValue::get(Inst->getType()));
      Inst->eraseFromParent();
    }
  }


  DEBUG(dbgs() << "Number of reductions = " << reductions.size() << "\n");

  BasicBlock* insert_before = &BB;
  for (reductions_t::iterator cur_reduction = reductions.begin();
       cur_reduction != reductions.end();
       ++cur_reduction ) {
    // Insert a loop into the function body
    insert_before = insert_loop( cur_reduction , &F , insert_before , &BB );
  }

  //F.dump();
#endif
  return true;
}




char qdp_jit_roll::ID = 0;
static RegisterPass<qdp_jit_roll> X(SV_NAME, "QDP-JIT roll linear code into loop");


ModulePass *llvm::create_qdp_jit_roll_pass() {
  return new qdp_jit_roll();
}


//INITIALIZE_PASS_BEGIN(qdp_jit_roll, "qdp-jit-roll", "QDP-JIT roll code into a new loop", false, false)
//INITIALIZE_AG_DEPENDENCY(AliasAnalysis)
//INITIALIZE_PASS_END(qdp_jit_roll, "qdp-jit-roll", "QDP-JIT roll code into a new loop", false, false)

