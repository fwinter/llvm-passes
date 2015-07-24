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
  }
  
  bool runOnModule(Module &M) override;

protected:
  struct reduction {
    SetVector<Value*> instructions;
    std::vector< std::vector<uint64_t> > offsets;  // outer: iteration, inner: GEP instruction within iteration
    int id;
  };
  typedef std::vector<reduction> reductions_t;

  void add_GEPs(BasicBlock &BB);
  bool track( SetVector<Value*>& set);
  void modify_loop_body( reduction& red , Value* ind_var , int64_t offset_normalize );
  BasicBlock* insert_loop( reductions_t::iterator cur , Function* F, BasicBlock* insert_before,BasicBlock* take_instr_from);

  SetVector<Value*> get_leaves( Value* V );
  SetVector<Value*> get_leaves( SetVector<Value*> V );
  SetVector<Value*> get_stores( Value* V );
  SetVector<Value*> get_stores( SetVector<Value*> V );
  SetVector<Value*> get_all_linked_stores_from_store( Value* V );
  SetVector<Value*> get_uses( Value* V );
  SetVector<Value*> get_uses( SetVector<Value*> V );


private:
  reductions_t reductions;
  Function* function;

  Module* module;
  typedef IRBuilder<true, TargetFolder> BuilderTy;
  LLVMContext *C;
  const DataLayout *DL;

  BuilderTy *Builder;
};
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
  std::vector<int64_t>  gep_GA_delta(gep_total_number);
  std::vector<size_t>   gep_GA_num(gep_total_number);    // match number within the match vector
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

  typedef std::pair< int64_t , size_t > PairDeltaGEPnum_t;  // delta, GEP num
  typedef std::pair< std::vector<int64_t> , std::vector< PairDeltaGEPnum_t > > Match_t; // offsets, GEP deltas

  std::vector< Match_t > matches;

  if (use_global_array) {

    SetVector<size_t> unmatched_gep;
    for ( size_t gep_num = 0 ; gep_num < gep_total_number ; ++gep_num ) {
      if ( !gep_cont[ gep_num ] ) {
	unmatched_gep.insert(gep_num);
      }
    }

    while (!unmatched_gep.empty()) {
      size_t gep_num0 = *unmatched_gep.begin();
      DEBUG(dbgs() << "Processing GEP_num=" << gep_num0 << "\n");
	  
      {
	std::vector<int64_t> offsets_gep0;
	for ( size_t it_num = 0 ; it_num < cur->offsets.size() ; ++it_num ) {
	  offsets_gep0.push_back( cur->offsets[it_num][gep_num0] );
	}
	matches.push_back( Match_t() );
	matches.back().first = std::move( offsets_gep0 );
	matches.back().second.push_back( std::make_pair( 0 , gep_num0 ) );
      }

      size_t gep1_start = *(unmatched_gep.begin()+1);
      DEBUG(dbgs() << "lo=" << gep1_start << " hi=" << gep1_start+unmatched_gep.size()-1 << "\n");

      for (size_t gep_num1 = gep1_start; gep_num1 < gep1_start+unmatched_gep.size()-1 ; ++gep_num1 ) {
	DEBUG(dbgs() << "Trying GEP " << gep_num0 << " and " << gep_num1 << "\n");
	
	bool match=true;
	int64_t diff = cur->offsets[0][gep_num1] - cur->offsets[0][gep_num0];
	for ( size_t it_num = 1 ; it_num < cur->offsets.size() && match ; ++it_num ) {
	  match = (diff == (int64_t)cur->offsets[it_num][gep_num1] - (int64_t)cur->offsets[it_num][gep_num0]);
	  if (!match) {
	    DEBUG(dbgs() << "no match on iteration " << it_num << "\n");
	  }
	}
      
	if (match) {
	  DEBUG(dbgs() << "new match: diff=" << diff << " GEP_num=" << gep_num1 << "\n");
	  matches.back().second.push_back( std::make_pair( diff , gep_num1 ) );
	  unmatched_gep.remove( gep_num1 );
	}
      }

      unmatched_gep.remove( gep_num0 );
      DEBUG(dbgs() << "unmatched_gep: ");
      for (size_t i : unmatched_gep) {
	DEBUG(dbgs() << i << " ");
      }
      DEBUG(dbgs() << "\n");
    }
  }

  DEBUG(dbgs() << "matches (GEP num,delta) :\n");
  for (size_t i = 0 ; i < matches.size() ; ++i ) {
    DEBUG(dbgs() << i << ": ");
    for (PairDeltaGEPnum_t p : matches[i].second) {
      DEBUG(dbgs() << p.second << "," << p.first << "  ");
      gep_GA_delta[p.second] = p.first;
      gep_GA_num[p.second] = i;
    }
    DEBUG(dbgs() << "\n");
  }
    
  std::vector<GlobalVariable*> offset_var( matches.size() );
  for (size_t match_it = 0 ; match_it < matches.size() ; ++match_it ) {
    Constant* CDA = ConstantDataArray::get( llvm::getGlobalContext() , 
					    ArrayRef<uint64_t>( (uint64_t*)matches[match_it].first.data() , 
								matches[match_it].first.size() ) );
    ArrayType *array_type = ArrayType::get( Type::getIntNTy(getGlobalContext(),64) , matches[match_it].first.size() );
    
    offset_var[match_it] = new GlobalVariable( *module, array_type , true, 
					       GlobalValue::InternalLinkage, CDA , "offset_array" );
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
  cond = Builder->CreateICmpUGE( PNp1 , ConstantInt::get( Type::getIntNTy(getGlobalContext(),64) , loop_count ) );
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
  std::vector<bool>   match_idx_loaded(matches.size());    // 
  std::vector<Value*> match_idx(matches.size());    // 

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

	if (!match_idx_loaded[ gep_GA_num[ gep_num ] ]) {
	  std::vector<Value*> tmp;
	  tmp.push_back( ConstantInt::get( Type::getIntNTy(getGlobalContext(),64) , 0 ) );
	  tmp.push_back( PN );
	  Builder->SetInsertPoint( PN->getNextNode() );
	  Value* offset_GEP = Builder->CreateGEP( offset_var.at( gep_GA_num[ gep_num ] ) , ArrayRef<Value*>(tmp) );
	  match_idx[ gep_GA_num[ gep_num ] ]   = Builder->CreateLoad( offset_GEP );
	  match_idx_loaded[ gep_GA_num[ gep_num ] ] = true;
	  Builder->SetInsertPoint(gep0);
	  DEBUG(dbgs() << "GEP num " << gep_num << " uses match num " << gep_GA_num[ gep_num ] << "\n" );
	}

	Value *new_gep_address = match_idx[ gep_GA_num[ gep_num ] ];
	if (gep_GA_delta[gep_num]) {
	  new_gep_address = Builder->CreateAdd( new_gep_address, ConstantInt::get( Type::getIntNTy(getGlobalContext(),64) , 
										   gep_GA_delta[gep_num] ) );
	}

	gep0->setOperand( 1 , new_gep_address );
      }
      gep_num++;
    }
  }

  //function->dump();


  return BB0;
}





SetVector<Value*> qdp_jit_roll::get_stores( Value* V )
{
  SetVector<Value*> stores;
  SetVector<Value*> to_visit;
  to_visit.insert(V);

  while (!to_visit.empty()) {
    Value* v = to_visit.back();
    to_visit.pop_back();
    Instruction* vi;
    if ((vi = dyn_cast<Instruction>(v))) {
      for (Use& U : vi->uses()) {
	if (isa<StoreInst>(U.getUser())) {
	  stores.insert(U.getUser());
	} else if (isa<Instruction>(U.getUser())) {
	  to_visit.insert(U.getUser());
	}
      }
    }
  }
  return stores;
}

SetVector<Value*> qdp_jit_roll::get_leaves( Value* V )
{
  SetVector<Value*> leaves;
  SetVector<Value*> to_visit;
  to_visit.insert(V);

  while (!to_visit.empty()) {
    Value* v = to_visit.back();
    to_visit.pop_back();
    Instruction* vi;
    if ((vi = dyn_cast<Instruction>(v))) {
      bool has_inst_op = false;
      for (Use& U : vi->operands()) {
	if (isa<Instruction>(U.get())) {
	  to_visit.insert(U.get());
	  has_inst_op = true;
	}
	if (!has_inst_op) {
	  leaves.insert(v);
	}
      }
    }
  }
  return leaves;
}

SetVector<Value*> qdp_jit_roll::get_leaves( SetVector<Value*> Vec )
{
  SetVector<Value*> leaves;
  for (Value* V : Vec) {
    SetVector<Value*> tmp = get_leaves( V );
    leaves.insert( tmp.begin() , tmp.end() );
  }
  return leaves;
}

SetVector<Value*> qdp_jit_roll::get_stores( SetVector<Value*> Vec )
{
  SetVector<Value*> stores;
  for (Value* V : Vec) {
    SetVector<Value*> tmp = get_stores( V );
    stores.insert( tmp.begin() , tmp.end() );
  }
  return stores;
}



SetVector<Value*> qdp_jit_roll::get_all_linked_stores_from_store( Value* V )
{
  bool all=false;
  SetVector<Value*> stores;
  stores.insert(V);
  while(!all) {
    SetVector<Value*> new_stores;
    new_stores = get_stores( get_leaves( stores ) );
    all = (new_stores.size() == stores.size());
    stores = new_stores;
  }
  return stores;
}


SetVector<Value*> qdp_jit_roll::get_uses( Value* V )
{
  SetVector<Value*> uses;
  SetVector<Value*> to_visit;
  to_visit.insert(V);
  uses.insert( V );

  while (!to_visit.empty()) {
    Value* v = to_visit.back();
    to_visit.pop_back();
    Instruction* vi;
    if ((vi = dyn_cast<Instruction>(v))) {
      for (Use& U : vi->uses()) {
	if (isa<Instruction>(U.getUser())) {
	  uses.insert(U.getUser());
	  to_visit.insert(U.getUser());
	}
      }
    }
  }
  return uses;
}

SetVector<Value*> qdp_jit_roll::get_uses( SetVector<Value*> Vec )
{
  SetVector<Value*> uses;
  for (Value* V : Vec) {
    SetVector<Value*> tmp = get_uses( V );
    uses.insert( tmp.begin() , tmp.end() );
  }
  return uses;
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

  int marked_erasure = 0;
  for (Instruction& I : BB) {
    if (isa<StoreInst>(I)) {
      if (processed.count( &I ) == 0 ) {

	DEBUG(dbgs() << "Found new StoreInst " << I << "\n");

	SetVector<Value*> DAG = get_uses( get_leaves( get_all_linked_stores_from_store( &I ) ) );
#if 0
	DEBUG(dbgs() << "DAG: " << "\n");
	for( Value* V : DAG ) {
	  DEBUG(dbgs() << *V << "\n");
	}
#endif
	DEBUG(dbgs() << "Whole DAG (inst. count) = " << DAG.size() << "\n");

	if (track(DAG)) {
	  for_erasure.insert( DAG.begin(), DAG.end() );
	  marked_erasure++;
	  //DEBUG(dbgs() << "Marked for erasure!" << "\n");
	}

	processed.insert(DAG.begin(),DAG.end());

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

