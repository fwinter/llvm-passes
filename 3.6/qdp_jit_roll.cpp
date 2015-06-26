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
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/ADT/SetVector.h"
#include <queue>
#include <vector>
#include <algorithm>

using namespace llvm;

#define DEBUG_TYPE "qdp_jit_roll"

//STATISTIC(NumLoadsAnalyzed, "Number of loads analyzed for combining");
//STATISTIC(NumLoadsCombined, "Number of loads combined");

namespace {


class qdp_jit_roll : public FunctionPass {
public:
  const char *getPassName() const override { return "qdp_jit_roll"; }
  static char ID;

  qdp_jit_roll()
      : FunctionPass(ID),
        C(nullptr), DL(nullptr) {
    initializeSROAPass(*PassRegistry::getPassRegistry());
  }
  
  //  using llvm::Pass::doInitialization;
  //bool doInitialization(Function &) override;
  bool runOnFunction(Function &F) override;

protected:
  struct reduction {
    SetVector<Value*> instructions;
    std::vector<int64_t> offsets;
  };

  void add_GEPs(BasicBlock &BB);
  void collectRoots( Instruction& I, SetVector<Value*>& all_roots);
  void collectAllUses( SetVector<Value*>& to_visit, SetVector<Value*>& all_uses);
  void collectAll( Instruction& I);
  void collectForStoresAllOperandsAll( SetVector<Value*>& tree );
  void collectAllInstructionOperands( SetVector<Value*>& roots, SetVector<Value*>& operands );
  bool track( SetVector<Value*>& set);
  void modify_loop_body( reduction& red , Value* ind_var , int64_t offset_normalize );
  //void getAnalysisUsage(AnalysisUsage &AU) const override;



private:
  std::vector<reduction> reductions;

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
  }
}



bool qdp_jit_roll::track( SetVector<Value*>& set) {
  if (reductions.empty()) {
    reductions.push_back( reduction() );
  }

  if (reductions[0].instructions.empty()) {
    reductions[0].instructions.insert( set.begin() , set.end() );
    reductions[0].offsets.push_back(0);
    return false;
  }

  reduction& cur_reduction = reductions[0];

  SetVector<Value*> reduction_stores;
  for (Value *v : cur_reduction.instructions ) {
    if (isa<StoreInst>(*v)) {
      reduction_stores.insert(v);
    }
  }
  SetVector<Value*> set_stores;
  for (Value *v : set ) {
    if (isa<StoreInst>(*v)) {
      set_stores.insert(v);
    }
  }

  assert(reduction_stores.size() == set_stores.size());

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
		      DEBUG(dbgs() << "found matching offsets " << off0 << " " << off1 << "\n");
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
	    if (cmp0_visit.size() != cmp1_visit.size())
	      mismatch=true;
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
    DEBUG(dbgs() << "use_set matches!" << "\n");
    cur_reduction.offsets.push_back( offset );
    return true;
  } else {
    DEBUG(dbgs() << "use_set doesn't match! Will add another reduction" << "\n");
    reductions.push_back( reduction() );
    reductions.back().instructions.insert( set.begin() , set.end() );
    reductions.back().offsets.push_back(0);
    return false;
  }
}



void qdp_jit_roll::modify_loop_body( reduction& red , Value* ind_var , int64_t offset_normalize )
{
  for( Value* V : red.instructions ) {
    if (GetElementPtrInst * gep0 = dyn_cast<GetElementPtrInst>(V)) {
      if (ConstantInt * ci0 = dyn_cast<ConstantInt>(gep0->getOperand(1))) {
	int64_t off0 = ci0->getZExtValue();
	int64_t off_new = off0 + offset_normalize;
	if (off_new) {
	  DEBUG(dbgs() << "Change offset " << off0 << " to " << off_new << "\n");
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



bool qdp_jit_roll::runOnFunction(Function &F) {
  DEBUG(dbgs() << "Running on F"  << "\n");

  BasicBlock& BB = F.getEntryBlock();

  IRBuilder<true, TargetFolder> TheBuilder(BB.getContext(), TargetFolder(DL));
  Builder = &TheBuilder;

  if (skipOptnoneFunction(F))
    return false;

  add_GEPs(BB);

  SetVector<Value*> all_roots;
  SetVector<Value*> processed;
  SetVector<Value*> for_erasure;


  for (Instruction& I : BB) {
    if (isa<StoreInst>(I)) {
      if (processed.count( &I ) == 0 ) {
	DEBUG(dbgs() << "Found new StoreInst " << I << "\n");
	collectRoots(I, all_roots);
	DEBUG(dbgs() << "Number of roots found " << all_roots.size() << "\n");
	SetVector<Value*> all_uses;
	collectAllUses(all_roots,all_uses);      
	collectForStoresAllOperandsAll(all_uses);

	DEBUG(dbgs() << "Number of all uses " << all_uses.size() << "\n");
	for (Value *v : all_uses)
	  DEBUG(dbgs() << *v << "\n");

	if (track(all_uses)) {
	  for_erasure.insert( all_uses.begin(), all_uses.end() );
	  DEBUG(dbgs() << "Use set will be erased!" << "\n");
	}
	

	processed.insert(all_uses.begin(),all_uses.end());
      } else {
	DEBUG(dbgs() << "Found already processed StoreInst " << I << "\n");
      }
      // for (Use& U : I.operands()) {
      // 	Value* V = U.get();
      // 	if (dyn_cast<Instruction>(V)) {
      // 	  DEBUG(dbgs() << "Found instruction " << *V << "\n");
      // 	} else {
      // 	  DEBUG(dbgs() << "Found operand " << *V << "\n");
      // 	}
      // }
      //use_empty = " << I.use_empty() << "\n");
    }
  }

  std::sort(reductions[0].offsets.begin(),reductions[0].offsets.end());
  DEBUG(dbgs() << "All offsets:\n");
  for ( auto offset : reductions[0].offsets ) {
    DEBUG(dbgs() << offset << " ");
  }
  DEBUG(dbgs() << "\n");

  auto offset_max = max_element(std::begin(reductions[0].offsets), std::end(reductions[0].offsets));
  auto offset_min = min_element(std::begin(reductions[0].offsets), std::end(reductions[0].offsets));
  auto offset_step = 0;
  int64_t offset_normalize = 0;

  if (*offset_min < 0) {
    DEBUG(dbgs() << "Found negative offsets, will normalize!\n");
    offset_normalize = *offset_min;
    for ( auto& offset : reductions[0].offsets ) {
      offset += offset_normalize;
    }
  }

  if (reductions[0].offsets.size() > 1) {
    offset_step = reductions[0].offsets[1] - reductions[0].offsets[0];

    for ( int64_t i = *offset_min ; i <= *offset_max ; i+=offset_step ) {
      if (std::find(reductions[0].offsets.begin(),reductions[0].offsets.end(),i ) == reductions[0].offsets.end()) {
	DEBUG(dbgs() << "Checking whether loop is contiguos.\n");
	DEBUG(dbgs() << "Iteration " << i << " not found! Can't roll code into a loop.\n");
	return false;
      }
    }
  }

  DEBUG(dbgs() 
	<< "Loop rolling is possible with: min = " << *offset_min 
	<< "   max = " << *offset_max 
	<< "  step = " << offset_step << "\n");  


  for ( Value* v: for_erasure ) {
    if (Instruction *Inst = dyn_cast<Instruction>(v)) {
      DEBUG(dbgs() << "erasure: " << *Inst << "\n");
      if (!Inst->use_empty())
	Inst->replaceAllUsesWith(UndefValue::get(Inst->getType()));
      Inst->eraseFromParent();
    }
  }

  ReturnInst* RI;
  for (Instruction& I : BB) {
    if (ReturnInst* RI0 = dyn_cast<ReturnInst>(&I)) {
      RI = RI0;
      DEBUG(dbgs() << "found ret " << *RI << "\n");
    }
  }
  RI->eraseFromParent();
  DEBUG(dbgs() << "done removing " << "\n");

  llvm::BasicBlock *BB0 = llvm::BasicBlock::Create(llvm::getGlobalContext(), "pre_loop" );
  F.getBasicBlockList().push_front(BB0);

  llvm::BasicBlock *BBe = llvm::BasicBlock::Create(llvm::getGlobalContext(), "exit_loop" );
  F.getBasicBlockList().push_back(BBe);
  Builder->SetInsertPoint(BBe);
  Builder->CreateRetVoid();

  Builder->SetInsertPoint(BB0);
  Builder->CreateBr(&BB);

  Builder->SetInsertPoint(&BB,BB.begin());
  PHINode * PN = Builder->CreatePHI( Type::getIntNTy(getGlobalContext(),64) , 2 );

  Builder->SetInsertPoint(&BB,BB.end());

  Value *PNp1 = Builder->CreateNSWAdd( PN , ConstantInt::get( Type::getIntNTy(getGlobalContext(),64) , offset_step ) );
  Value *cond = Builder->CreateICmpUGT( PNp1 , ConstantInt::get( Type::getIntNTy(getGlobalContext(),64) , *offset_max ) );

  PN->addIncoming( ConstantInt::get( Type::getIntNTy(getGlobalContext(),64) , *offset_min ) , BB0 );
  PN->addIncoming( PNp1 , &BB );

  Builder->CreateCondBr( cond , BBe, &BB);
  

  modify_loop_body( reductions[0] , PN , offset_normalize );


  F.dump();

  //AA = &getAnalysis<AliasAnalysis>();


  return true;
}



// void qdp_jit_roll::getAnalysisUsage(AnalysisUsage &AU) const {
//   AU.setPreservesCFG();

//   AU.addRequired<AliasAnalysis>();
//   AU.addPreserved<AliasAnalysis>();
// }


char qdp_jit_roll::ID = 0;
static RegisterPass<qdp_jit_roll> X("qdp_jit_roll", "QDP-JIT roll linear code into loop");


FunctionPass *llvm::create_qdp_jit_roll_pass() {
  return new qdp_jit_roll();
}


//INITIALIZE_PASS_BEGIN(qdp_jit_roll, "qdp-jit-roll", "QDP-JIT roll code into a new loop", false, false)
//INITIALIZE_AG_DEPENDENCY(AliasAnalysis)
//INITIALIZE_PASS_END(qdp_jit_roll, "qdp-jit-roll", "QDP-JIT roll code into a new loop", false, false)

