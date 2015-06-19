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

using namespace llvm;

#define DEBUG_TYPE "qdp_jit_roll"

//STATISTIC(NumLoadsAnalyzed, "Number of loads analyzed for combining");
//STATISTIC(NumLoadsCombined, "Number of loads combined");

namespace {


class qdp_jit_roll : public BasicBlockPass {
  LLVMContext *C;
  const DataLayout *DL;
  //  AliasAnalysis *AA;

public:
  qdp_jit_roll()
      : BasicBlockPass(ID),
        C(nullptr), DL(nullptr) {
    initializeSROAPass(*PassRegistry::getPassRegistry());
  }
  
  using llvm::Pass::doInitialization;
  bool doInitialization(Function &) override;
  bool runOnBasicBlock(BasicBlock &BB) override;
  void add_GEPs(BasicBlock &BB);
  void collectRoots( Instruction& I, SetVector<Value*>& all_roots);
  void collectAllUses( SetVector<Value*>& to_visit, SetVector<Value*>& all_uses);
  void collectAll( Instruction& I);
  void collectForStoresAllOperandsAll( SetVector<Value*>& tree );
  void collectAllInstructionOperands( SetVector<Value*>& roots, SetVector<Value*>& operands );
  //void getAnalysisUsage(AnalysisUsage &AU) const override;

  const char *getPassName() const override { return "qdp_jit_roll"; }
  static char ID;

  typedef IRBuilder<true, TargetFolder> BuilderTy;

private:
  BuilderTy *Builder;

  //PointerOffsetPair getPointerOffsetPair(LoadInst &);
  //bool combineLoads(DenseMap<const Value *, SmallVector<LoadPOPPair, 8>> &);
  //bool aggregateLoads(SmallVectorImpl<LoadPOPPair> &);
  //bool combineLoads(SmallVectorImpl<LoadPOPPair> &);
};
}

bool qdp_jit_roll::doInitialization(Function &F) {
  DEBUG(dbgs() << "qdp_jit_roll function: " << F.getName() << "\n");
  C = &F.getContext();
  DataLayoutPass *DLP = getAnalysisIfAvailable<DataLayoutPass>();
  if (!DLP) {
    DEBUG(dbgs() << "  Skipping qdp_jit_roll -- no target data!\n");
    return false;
  }
  DL = &DLP->getDataLayout();
  return true;
}




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




bool qdp_jit_roll::runOnBasicBlock(BasicBlock &BB) {
  DEBUG(dbgs() << "Running on BB"  << "\n");

  IRBuilder<true, TargetFolder> TheBuilder(BB.getContext(), TargetFolder(DL));
  Builder = &TheBuilder;

  if (skipOptnoneFunction(BB) || !DL)
    return false;

  add_GEPs(BB);

  SetVector<Value*> all_roots;


  for (Instruction& I : BB) {
    if (isa<StoreInst>(I)) {
      DEBUG(dbgs() << "Found StoreInst " << I << "\n");
      collectRoots(I, all_roots);
      DEBUG(dbgs() << "Number of roots found " << all_roots.size() << "\n");
      SetVector<Value*> all_uses;
      collectAllUses(all_roots,all_uses);      
      collectForStoresAllOperandsAll(all_uses);

      DEBUG(dbgs() << "Number of all uses " << all_uses.size() << "\n");
      for (Value *v : all_uses)
	DEBUG(dbgs() << *v << "\n");

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


BasicBlockPass *llvm::create_qdp_jit_roll_pass() {
  return new qdp_jit_roll();
}


//INITIALIZE_PASS_BEGIN(qdp_jit_roll, "qdp-jit-roll", "QDP-JIT roll code into a new loop", false, false)
//INITIALIZE_AG_DEPENDENCY(AliasAnalysis)
//INITIALIZE_PASS_END(qdp_jit_roll, "qdp-jit-roll", "QDP-JIT roll code into a new loop", false, false)

