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

#define DEBUG_TYPE "qdp_jit_roll"

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
    initializeSROAPass(*PassRegistry::getPassRegistry());
  }
  
  //  using llvm::Pass::doInitialization;
  //bool doInitialization(Function &) override;
  //bool runOnFunction(Function &F) override;
  bool runOnModule(Module &M) override;

protected:
  struct reduction {
    SetVector<Value*> instructions;
    std::vector<uint64_t> offsets;
    int id;
  };
  typedef std::vector<reduction> reductions_t;

  void add_GEPs(BasicBlock &BB);
  void collectRoots( Instruction& I, SetVector<Value*>& all_roots);
  void collectAllUses( SetVector<Value*>& to_visit, SetVector<Value*>& all_uses);
  void collectAll( Instruction& I);
  void collectForStoresAllOperandsAll( SetVector<Value*>& tree );
  void collectAllInstructionOperands( SetVector<Value*>& roots, SetVector<Value*>& operands );
  bool track( SetVector<Value*>& set);
  void modify_loop_body( reduction& red , Value* ind_var , int64_t offset_normalize );
  //bool insert_loop( reductions_t::iterator cur , Function* F, BasicBlock* successor);
  BasicBlock* insert_loop( reductions_t::iterator cur , Function* F, BasicBlock* insert_before,BasicBlock* take_instr_from);
  //void getAnalysisUsage(AnalysisUsage &AU) const override;



private:
  reductions_t reductions;

  Module* module;
  typedef IRBuilder<true, TargetFolder> BuilderTy;
  LLVMContext *C;
  const DataLayout *DL;
  //  AliasAnalysis *AA;

  BuilderTy *Builder;


  //PointerOffsetPair getPointerOffsetPair(LoadInst &);
  //bool combineLoads(DenseMap<const Value *, SmallVector<LoadPOPPair, 8>> &);
  //bool aggregateLoads(SmallVectorImpl<LoadPOPPair> &);
  //bool combineLoads(SmallVectorImpl<LoadPOPPair> &);
};
}

// bool qdp_jit_roll::doInitialization(Function &F) {
//   DEBUG(dbgs() << "qdp_jit_roll function: " << F.getName() << "\n");
//   C = &F.getContext();
//   DataLayoutPass *DLP = getAnalysisIfAvailable<DataLayoutPass>();
//   if (!DLP) {
//     DEBUG(dbgs() << "  Skipping qdp_jit_roll -- no target data!\n");
//     return false;
//   }
//   DL = &DLP->getDataLayout();
//   return true;
// }




void qdp_jit_roll::collectAll( Instruction& I) {
  DEBUG(dbgs() << "collectAll for " << I << "\n");

  std::vector<Value*> all_deps;
  std::queue<Value*> to_visit;

  to_visit.push(&I);

  while (!to_visit.empty()) {
    Value* v = to_visit.front();
    to_visit.pop();
    Instruction* vi;
    if ((vi = dyn_cast<Instruction>(v))) {
      DEBUG(dbgs() << "Found instruction " << *vi << "\n");
      all_deps.push_back(v);
      for (Use& U : vi->operands()) {
	to_visit.push(U.get());
      }
    }
  }
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
// else {
//       if (!isa<Constant>(v)) {
// 	DEBUG(dbgs() << "Found a non-instruction,non-constant " << *v << "\n");
// 	all_roots.insert(v);
//       }
//}


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
  DEBUG(dbgs() << "\n Track set with " << set.size() << " instructions.\n");

  static int id;

  if (reductions.empty()) {
    reductions.push_back( reduction() );
    reductions[0].instructions.insert( set.begin() , set.end() );
    reductions[0].offsets.push_back(0);
    reductions[0].id = id++;
    return false;
  }


  bool reduction_found = false;

  for (reductions_t::iterator cur_reduction = reductions.begin();
       cur_reduction != reductions.end() && !reduction_found ; 
       ++cur_reduction ) {

    DEBUG(dbgs() << "Trying reduction " << cur_reduction->id << "\n");

    DEBUG(dbgs() << "current reduction: " << "\n");
    SetVector<Value*> reduction_stores;
    for (Value *v : cur_reduction->instructions ) {
      DEBUG(dbgs() << *v << "\n");
      if (isa<StoreInst>(*v)) {
	reduction_stores.insert(v);
      }
    }
    DEBUG(dbgs() << "incoming set: " << "\n");
    SetVector<Value*> set_stores;
    for (Value *v : set ) {
      DEBUG(dbgs() << *v << "\n");
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
    bool offset_set = false;
    int64_t offset = 0;

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
	    
	      if (Instruction * gep0 = dyn_cast<GetElementPtrInst>(v0)) {
		if (Instruction * gep1 = dyn_cast<GetElementPtrInst>(v1)) {
		  //DEBUG(dbgs() << "found GEPs " << *gep0 << " " << *gep1 << "\n");
		  //DEBUG(dbgs() << "ops " << *gep0->getOperand(1) << " " << *gep1->getOperand(1) << "\n");
		  if (ConstantInt * ci0 = dyn_cast<ConstantInt>(gep0->getOperand(1))) {
		    if (ConstantInt * ci1 = dyn_cast<ConstantInt>(gep1->getOperand(1))) {
		      int64_t off0 = ci0->getZExtValue();
		      int64_t off1 = ci1->getZExtValue();
		      //DEBUG(dbgs() << "found Ints " << off0 << " " << off1 << "\n");
		      if (offset_set) {
			if ( off0-off1 != offset && off0-off1 != 0 ) {
			  DEBUG(dbgs() << "found non-matching offsets " << off0 << " " << off1 << "\n");
			  mismatch = true;
			}
		      } else {
			offset = off0 - off1;
			offset_set = true;
			//DEBUG(dbgs() << "found offsets " << off0 << " " << off1 << "\n");
		      }
		    }
		  }
		}
	      }

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
      if (offset < 0) {
	DEBUG(dbgs() << "found a negative offset " << offset << ". That's not supported\n");
	exit(0);
      }
      DEBUG(dbgs() << " -> use_set matches, add offset " << offset << "\n");
      cur_reduction->offsets.push_back( offset );
      reduction_found = true;
      break;
    } 
  }

  if (reduction_found)
    return true;

  DEBUG(dbgs() << "use_set doesn't match! Will add another reduction" << "\n");
  reductions.push_back( reduction() );
  reductions.back().instructions.insert( set.begin() , set.end() );
  reductions.back().offsets.push_back(0);
  reductions.back().id = id++;
  return false;
}




void qdp_jit_roll::modify_loop_body( reduction& red , Value* ind_var , int64_t offset_normalize )
{
  for( Value* V : red.instructions ) {
    if (GetElementPtrInst * gep0 = dyn_cast<GetElementPtrInst>(V)) {
      if (ConstantInt * ci0 = dyn_cast<ConstantInt>(gep0->getOperand(1))) {
	int64_t off0 = ci0->getZExtValue();
	int64_t off_new = off0 + offset_normalize;
	if (off_new) {
	  //DEBUG(dbgs() << "Change offset " << off0 << " to " << off_new << "\n");
	  Builder->SetInsertPoint(gep0);
	  Value *new_gep_address = Builder->CreateAdd( ind_var , 
						       ConstantInt::get( Type::getIntNTy(getGlobalContext(),64) , 
									 off0 + offset_normalize ) );
	  gep0->setOperand( 1 , new_gep_address );
	} else {
	  gep0->setOperand( 1 , ind_var );
	}
      }
    }
  }
}


//
// returns the block (loop start) that was inserted
//
BasicBlock* qdp_jit_roll::insert_loop( reductions_t::iterator cur , Function* F, BasicBlock* insert_before,BasicBlock* take_instr_from)
{
  auto offset_max = max_element(std::begin(cur->offsets), std::end(cur->offsets));
  auto offset_min = min_element(std::begin(cur->offsets), std::end(cur->offsets));
  auto offset_step = 0;

  
  bool constant_stride=true;
  uint64_t loop_count;
  GlobalVariable* offset_var;

  if (cur->offsets.size() > 1) {
    offset_step = cur->offsets[1] - cur->offsets[0];
      
    for ( uint64_t i = *offset_min ; i <= *offset_max ; i+=offset_step ) {
      if (std::find(cur->offsets.begin(),cur->offsets.end(),i ) == cur->offsets.end()) {
	DEBUG(dbgs() << "Checking whether loop is contiguos.\n");
	DEBUG(dbgs() << "Iteration " << i << " not found! Must use and offset array.\n");
	Constant* CDA = ConstantDataArray::get( llvm::getGlobalContext() , 
						ArrayRef<uint64_t>( cur->offsets.data() , cur->offsets.size() ) );
	ArrayType *array_type = ArrayType::get( Type::getIntNTy(getGlobalContext(),64) , cur->offsets.size() );

	offset_var = new GlobalVariable(*module, array_type , true, GlobalValue::InternalLinkage, CDA , "offset_array" );

	constant_stride = false;
	loop_count = cur->offsets.size();

	break;
      }
    }
  }


  DEBUG(dbgs() 
	<< "Loop rolling is possible with: min = " << *offset_min 
	<< "   max = " << *offset_max 
	<< "  step = " << offset_step << "\n");  
    
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

  BasicBlock::iterator inst_set_begin;
  bool notfound = true;
  for (inst_set_begin = take_instr_from->begin() ; inst_set_begin != take_instr_from->end() ; ++inst_set_begin ) {
    if (cur->instructions.count(inst_set_begin)) {
      notfound = false;
      break;
    }
  }
  if (notfound) {
    DEBUG(dbgs() << "Could not find any instruction in the basic block that is also in the current set.\n" );    
    return NULL;
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


  Value *cond;
  Value *PNp1;
  Value * offset_read;
  if (constant_stride) {
    PNp1 = Builder->CreateNSWAdd( PN , ConstantInt::get( Type::getIntNTy(getGlobalContext(),64) , offset_step ) );
    cond = Builder->CreateICmpUGT( PNp1 , ConstantInt::get( Type::getIntNTy(getGlobalContext(),64) , *offset_max ) );
    PN->addIncoming( ConstantInt::get( Type::getIntNTy(getGlobalContext(),64) , *offset_min ) , BB0 );
    PN->addIncoming( PNp1 , BBl );
  } else {
    std::vector<Value*> tmp;
    tmp.push_back( ConstantInt::get( Type::getIntNTy(getGlobalContext(),64) , 0 ) );
    tmp.push_back( PN );
    Value* offset_GEP = Builder->CreateGEP( offset_var , ArrayRef<Value*>(tmp) );
    offset_read = Builder->CreateLoad( offset_GEP );

    PNp1 = Builder->CreateNSWAdd( PN , ConstantInt::get( Type::getIntNTy(getGlobalContext(),64) , 1 ) );
    cond = Builder->CreateICmpUGE( PNp1 , ConstantInt::get( Type::getIntNTy(getGlobalContext(),64) , loop_count ) );
    PN->addIncoming( ConstantInt::get( Type::getIntNTy(getGlobalContext(),64) , 0 ) , BB0 );
    PN->addIncoming( PNp1 , BBl );
  }

  Builder->CreateCondBr( cond , BBe, BBl);

  BBl->getInstList().splice( cast<Instruction>(PNp1) , take_instr_from->getInstList() , inst_set_begin , inst_set_end );

  if (constant_stride) {
    modify_loop_body( *cur , PN , 0 );
  } else {
    modify_loop_body( *cur , offset_read , 0 );
  }

  DEBUG(dbgs() << "Latch after splice & modify:\n" );    
  BBl->dump();

  return BB0;
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


#if 0
	for (Value *v : all_uses)
	  DEBUG(dbgs() << *v << "\n");
#endif

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


  int i=0;
  DEBUG(dbgs() << "Number of reductions = " << reductions.size() << "\n");
  for (reductions_t::iterator cur_reduction = reductions.begin();
       cur_reduction != reductions.end(); 
       ++cur_reduction,++i ) {
    DEBUG(dbgs() << "All offsets for reduction " << i << ": ");
    if (cur_reduction->offsets.size() > 24) {
      DEBUG(dbgs() << cur_reduction->offsets[0] << " ");
      DEBUG(dbgs() << cur_reduction->offsets[1] << " ");
      DEBUG(dbgs() << " ... ");
      DEBUG(dbgs() << cur_reduction->offsets[cur_reduction->offsets.size()-2] << " ");
      DEBUG(dbgs() << cur_reduction->offsets[cur_reduction->offsets.size()-1] << " ");
    } else {
      for ( auto offset : cur_reduction->offsets ) {
	DEBUG(dbgs() << offset << " ");
      }
    }
    DEBUG(dbgs() << "\n");
  }

  BasicBlock* insert_before = &BB;
  for (reductions_t::iterator cur_reduction = reductions.begin();
       cur_reduction != reductions.end();
       ++cur_reduction ) {
    // Insert a loop into the function body
    insert_before = insert_loop( cur_reduction , &F , insert_before , &BB );
  }

  //  F.dump();
#endif
  return true;
}



// void qdp_jit_roll::getAnalysisUsage(AnalysisUsage &AU) const {
//   AU.setPreservesCFG();

//   AU.addRequired<AliasAnalysis>();
//   AU.addPreserved<AliasAnalysis>();
// }


char qdp_jit_roll::ID = 0;
static RegisterPass<qdp_jit_roll> X("qdp_jit_roll", "QDP-JIT roll linear code into loop");


ModulePass *llvm::create_qdp_jit_roll_pass() {
  return new qdp_jit_roll();
}


//INITIALIZE_PASS_BEGIN(qdp_jit_roll, "qdp-jit-roll", "QDP-JIT roll code into a new loop", false, false)
//INITIALIZE_AG_DEPENDENCY(AliasAnalysis)
//INITIALIZE_PASS_END(qdp_jit_roll, "qdp-jit-roll", "QDP-JIT roll code into a new loop", false, false)

