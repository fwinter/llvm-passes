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

#define SV_NAME "qdp_jit_vec"
#define DEBUG_TYPE SV_NAME


namespace {


class qdp_jit_vec : public FunctionPass {
public:
  const char *getPassName() const override { return "qdp_jit_vec"; }
  static char ID;

  qdp_jit_vec()
      : FunctionPass(ID),
        C(nullptr), DL(nullptr), vector_length(4) {}
  
  bool runOnFunction(Function &F) override;

protected:
  struct reduction {
    reduction( StoreInst* SI, int64_t off ): lo(off), hi(off+1) {
      instructions.push_back( SI );
    }
    std::vector<StoreInst*> instructions;
    int64_t lo,hi;
  };
  typedef std::vector<reduction> reductions_t;
  typedef std::vector<reduction>::iterator reductions_iterator;

  void track( StoreInst* SI , int64_t offset );
  void vectorize( reductions_iterator red );
  int vectorize_loads( std::vector<std::vector<Instruction*> >& load_instructions);
  void vectorize_all_uses( std::vector<Value*> vector_loads );
  void mark_for_erasure_all_operands(Value* V);

private:
  reductions_t reductions;
  SetVector<Value*> for_erasure;

  Module* module;
  typedef IRBuilder<true, TargetFolder> BuilderTy;
  LLVMContext *C;
  const DataLayout *DL;
  BuilderTy *Builder;
  int64_t vector_length;
};
}



bool is_visit_vector_non_empty(std::vector<SetVector<Value*> >& visit)
{
  if (visit.empty()) {
    DEBUG(dbgs() << "visit vector is empty." << "\n");
    exit(0);
  }
  size_t number = visit.at(0).size();
  DEBUG(dbgs() << "visit vector size = " << number << "\n");
  for ( SetVector<Value*>& SV : visit ) {
    if (SV.empty())
      return false;
    if (SV.size() != number)
      return false;
  }
  return true;
}


bool get_last_elements_as_instructions(std::vector<SetVector<Value*> >& visit , std::vector<Instruction*>& vi )
{
  if (visit.empty()) {
    DEBUG(dbgs() << "visit vector empty!\n");
    return false;
  }
  vi.clear();
  unsigned opcode;
  Instruction* i_save;
  bool first=true;
  for( SetVector<Value*>& sv : visit ) {
    if (Instruction * i = dyn_cast<Instruction>(sv.back())) {
      DEBUG(dbgs() << *i << "  ");
      vi.push_back(i);
      sv.pop_back();
      if (first) {
	opcode = i->getOpcode();
	first=false;
	i_save = i;
      } else {
	if (opcode != i->getOpcode()) {
	  DEBUG(dbgs() << "mismatching opcode " << *i << " " << *i_save << "\n");
	  return false;
	}
      }
    }
    else {
      DEBUG(dbgs() << "not an instruction: " << *sv.back() << "\n");
      return false;
    }
  }
  DEBUG(dbgs() << "\n");
  return true;
}




void qdp_jit_vec::vectorize_all_uses( std::vector<Value*> vector_loads )
{
  Value* VLI = vector_loads.at(0);

  DEBUG(dbgs() << "VLI type " << *VLI->getType() << "\n");

  SetVector<Value*> to_visit;
  for( Value* V: vector_loads ) {
    for (Use &U : V->uses()) {
      Value* VU = U.getUser();
      to_visit.insert(VU);
    }
  }
 
  while (!to_visit.empty()) {
    Value* V = to_visit.back();
    DEBUG(dbgs() << "to_visit size " << to_visit.size() << " visiting " << *V << "\n");
    //all_uses.insert(v);
    to_visit.pop_back();

    if (isa<StoreInst>(V)) {

      StoreInst* SI = cast<StoreInst>(V);
      unsigned AS = SI->getPointerAddressSpace();

      SequentialType* ST = cast<SequentialType>(SI->getPointerOperand()->getType());
      //DEBUG(dbgs() << "store pointer operand type: " << *ST->getElementType() << "\n");
      if (!isa<VectorType>(ST->getElementType())) {
	DEBUG(dbgs() << "store: " << *SI << "\n");

	// DEBUG(dbgs() << "store value:   " << *SI->getValueOperand() << "\n");
	// DEBUG(dbgs() << "store pointer: " << *SI->getPointerOperand() << "\n");
      
	Type* VecTy = SI->getValueOperand()->getType();

	Builder->SetInsertPoint( SI );      
	Value *VecPtr   = Builder->CreateBitCast(SI->getPointerOperand(),VecTy->getPointerTo(AS));
	SI->setOperand(1,VecPtr);
      } else {
	DEBUG(dbgs() << "is already a vector store: " << *SI << "\n");
      }

    } else {
      V->mutateType( VLI->getType() );
      for (Use &U : V->uses()) {
	Value* VU = U.getUser();
	to_visit.insert(VU);
      }
    }
  }
}




int qdp_jit_vec::vectorize_loads( std::vector<std::vector<Instruction*> >& load_instructions)
{
  std::vector<Value*> vector_loads;
  if (load_instructions.empty())
    return 0;
  int vec_len = load_instructions.at(0).size();
  int load_vec_elem = 0;
  int loads_consec = true;
  for( std::vector<Instruction*>& VI : load_instructions ) {
    DEBUG(dbgs() << "Processing vector of loads number " << load_vec_elem++ << "\n");
    uint64_t lo,hi;
    GetElementPtrInst* first_GEP;
    bool first = true;
    for( Instruction* I : VI ) {
      GetElementPtrInst* GEP;
      if ((GEP = dyn_cast<GetElementPtrInst>(I->getOperand(0)))) {
	if (first) {
	  first_GEP=GEP;
	  ConstantInt * CI;
	  if ((CI = dyn_cast<ConstantInt>(GEP->getOperand(1)))) {
	    lo = CI->getZExtValue();
	    hi = lo+1;
	    first=false;
	  } else {
	    DEBUG(dbgs() << "First load in the chain: Operand of GEP not a ConstantInt" << *GEP->getOperand(1) << "\n");
	    loads_consec = false;
	  }
	} else {
	  ConstantInt * CI;
	  if ((CI = dyn_cast<ConstantInt>(GEP->getOperand(1)))) {
	    if (hi != CI->getZExtValue()) {
	      DEBUG(dbgs() << "Loads not consecutive lo=" << lo << " hi=" << hi << " this=" << CI->getZExtValue() << "\n");
	      loads_consec = false;
	    } else {
	      hi++;
	    }
	  }
	}
      } else {
	DEBUG(dbgs() << "Operand of load not a GEP " << *I->getOperand(0) << "\n");
	loads_consec = false;
      }
    }
    if (loads_consec) {
      DEBUG(dbgs() << "Loads consecuetive\n");

      LoadInst* LI = cast<LoadInst>(VI.at(0));
      unsigned AS = LI->getPointerAddressSpace();
      VectorType *VecTy = VectorType::get( LI->getType() , vec_len );
      Builder->SetInsertPoint( LI );
      Value *VecPtr = Builder->CreateBitCast(LI->getPointerOperand(),VecTy->getPointerTo(AS));
      //Value *VecLoad = Builder->CreateLoad( VecPtr );
      LI->setOperand(0,VecPtr);
      LI->mutateType(VecTy);

      vector_loads.push_back( LI );
    } else {
      DEBUG(dbgs() << "Loads not consecutive\n");
    }
  }

  vectorize_all_uses( vector_loads );

  return 0;
}



void qdp_jit_vec::mark_for_erasure_all_operands(Value* V)
{
  std::queue<Value*> to_visit;

  to_visit.push(V);

  while (!to_visit.empty()) {
    Value* v = to_visit.front();
    to_visit.pop();
    Instruction* vi;
    if ((vi = dyn_cast<Instruction>(v))) {
      DEBUG(dbgs() << "Found instruction " << *vi << "\n");
      for_erasure.insert(v);
      for (Use& U : vi->operands()) {
	to_visit.push(U.get());
      }
    }
  }
}



void qdp_jit_vec::vectorize( reductions_iterator red )
{
  int vec_len = red->hi - red->lo;

  std::vector<std::vector<Instruction*> > load_instructions;

  SetVector<Value*> to_erase;
  std::vector<SetVector<Value*> > visit(vec_len);
  int i=0;
  for ( StoreInst* SI : red->instructions ) {
    if (i>0)
      to_erase.insert(SI);
    DEBUG(dbgs() << "insert to visit " << *SI << "\n");
    visit[i++].insert( cast<Value>(SI) );
  }

  bool mismatch=false;
  while ( is_visit_vector_non_empty(visit) && !mismatch ) {

    std::vector<Instruction*> vi;
    if (!get_last_elements_as_instructions(visit,vi)) {
      mismatch=true;
      break;
    }

    if (isa<LoadInst>(vi.at(0))) {
      load_instructions.push_back(vi);
    } else {
      for (size_t i=0 ; i < vi.size() ; ++i ) {
	for (Use& u : vi[i]->operands()) {
	  if (isa<Instruction>(u.get())) {
	    visit[i].insert(u.get());
	  }
	}
      }
    }
  }

  if (mismatch) {
     DEBUG(dbgs() << "mismatch!\n");
  } else {
     DEBUG(dbgs() << "match!\n");
     int successful = vectorize_loads( load_instructions );
     DEBUG(dbgs() << "vectorization successful on " << successful << " sets of load instructions\n");
  }

  DEBUG(dbgs() << "to_erase:\n");
  for ( Value* V : to_erase ) {
    DEBUG(dbgs() << *V << "\n");
    mark_for_erasure_all_operands(V);
  }

}



void qdp_jit_vec::track( StoreInst* SI , int64_t offset )
{
  if (reductions.empty()) {
    reduction r(SI,offset);
    reductions.push_back(r);
    return;
  }
  reductions_iterator red_match;
  bool found=false;
  for (reductions_iterator r = reductions.begin() ; r != reductions.end() ; ++r ) {
    if ( r->hi == offset ) {
      r->instructions.push_back( SI );
      r->hi++;
      if (r->hi - r->lo == vector_length) {
	DEBUG(dbgs() << "Found vectorization!" << "\n");
	red_match = r;
	found=true;
      }
    }
  }
  if (found) {
    DEBUG(dbgs() << "Do vectorization..." << "\n");
    vectorize( red_match );
    DEBUG(dbgs() << "Remove reduction..." << "\n");
    reductions.erase( red_match );
  }
}



bool qdp_jit_vec::runOnFunction(Function &F) {
  //DEBUG(dbgs() << "qdp_jit_vec running on Function " << F << "\n");
  //module = &M;
  IRBuilder<true, TargetFolder> TheBuilder(F.getContext(), TargetFolder(DL));
  Builder = &TheBuilder;

  BasicBlock& BB = F.getEntryBlock();

  Builder->SetInsertPoint(&BB,BB.begin());

  for (Instruction& I : BB) {
    if (StoreInst* SI = dyn_cast<StoreInst>(&I)) {
      Value* V = SI->getOperand(1);
      if (GetElementPtrInst* GEP = dyn_cast<GetElementPtrInst>(V)) {
	//DEBUG(dbgs() << "Found GEP " << *GEP << "\n");
	if (ConstantInt * CI = dyn_cast<ConstantInt>(GEP->getOperand(1))) {
	  int64_t off = CI->getZExtValue();
	  //DEBUG(dbgs() << " number = " << off << "\n");
	  track( SI , off );
	}
      }
    }
  }

  DEBUG(dbgs() << "Erasing instruction count = " << for_erasure.size() << "\n");
  for ( Value* v: for_erasure ) {
    if (Instruction *Inst = dyn_cast<Instruction>(v)) {
      //DEBUG(dbgs() << "erasure: " << *Inst << "\n");
      if (!Inst->use_empty())
	Inst->replaceAllUsesWith(UndefValue::get(Inst->getType()));
      Inst->eraseFromParent();
    }
  }

  return true;
}


char qdp_jit_vec::ID = 0;
static RegisterPass<qdp_jit_vec> X(SV_NAME, "QDP-JIT vectorize code");


#if 0
FunctionPass *llvm::create_qdp_jit_vec_pass() {
  return new qdp_jit_vec();
}
#endif


//INITIALIZE_PASS_BEGIN(qdp_jit_vec, "qdp-jit-roll", "QDP-JIT roll code into a new loop", false, false)
//INITIALIZE_AG_DEPENDENCY(AliasAnalysis)
//INITIALIZE_PASS_END(qdp_jit_vec, "qdp-jit-roll", "QDP-JIT roll code into a new loop", false, false)

