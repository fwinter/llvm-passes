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
#include <deque>

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
  int vectorize_loads( std::vector<std::vector<Instruction*> >& load_instructions );
  //void vectorize_all_uses( std::vector<Value*> vector_loads );
  void vectorize_all_uses( std::vector<std::pair<Value*,Value*> > scalar_vector_loads);
  void mark_for_erasure_all_operands(Value* V);
  void move_inst_before(Instruction* to_move,Instruction* before);
  Instruction* clone_with_operands(Instruction* to_clone,Instruction* insert_point);
  Instruction* clone_with_operands(Instruction* to_clone); // uses Builder
  Value* get_vector_version( Value* scalar_version );

private:
  reductions_t reductions;
  SetVector<Value*> for_erasure;
  SetVector<Value*> stores_processed;
  Function* function;
  BasicBlock* orig_BB;
  BasicBlock* vec_BB;

  std::vector<std::pair<Value*,Value*> > scalar_vector_pairs;

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



Value* qdp_jit_vec::get_vector_version( Value* scalar_version )
{
  DEBUG(dbgs() << "get_vector_version: scalar version: " << *scalar_version << "\n");

  if (StoreInst* SI = dyn_cast<StoreInst>(scalar_version)) {
    unsigned AS = SI->getPointerAddressSpace();

    SequentialType* ST = cast<SequentialType>(SI->getPointerOperand()->getType());
    //DEBUG(dbgs() << "store pointer operand type: " << *ST->getElementType() << "\n");
    if (isa<VectorType>(ST->getElementType())) {
      assert( 0 && "did not expect a vector type store instruction" );
    }

    //DEBUG(dbgs() << "store:        " << *SI << "\n");

    // DEBUG(dbgs() << "store value:   " << *SI->getValueOperand() << "\n");
    // DEBUG(dbgs() << "store pointer: " << *SI->getPointerOperand() << "\n");

    Instruction* GEP = cast<Instruction>(SI->getPointerOperand());

    Instruction* GEPcl = clone_with_operands( GEP );

    Value* vec_value  = get_vector_version( SI->getValueOperand() );
    Value *VecPtr     = Builder->CreateBitCast( GEPcl , vec_value->getType()->getPointerTo(AS) );
    Value* vecstore = Builder->CreateStore( vec_value , VecPtr );
    DEBUG(dbgs() << "vec store created " << *vecstore << "\n");
    return vecstore;
  }

  for ( std::vector<std::pair<Value*,Value*> >::iterator it = scalar_vector_pairs.begin();
	it != scalar_vector_pairs.end();
	++it ) {
    DEBUG(dbgs() << "search: " << *it->first << "\n");
    if ( it->first == scalar_version ) {
      DEBUG(dbgs() << "found it, it was already there!\n");
      return it->second;
    }
  }


  Instruction* I = cast<Instruction>(scalar_version);

  std::vector<Value*> operands;
  for (Use& U : I->operands()) 
    operands.push_back(U.get());

  //I->getOperand(0);

  unsigned Opcode = I->getOpcode();
  switch (Opcode) {
  case Instruction::FMul: {
    Value* V = Builder->CreateFMul( get_vector_version( operands.at(0) ) ,
				    get_vector_version( operands.at(1) ) );
    scalar_vector_pairs.push_back( std::make_pair( I , V ) );
    DEBUG(dbgs() << "vec mul created " << *V << "\n");
    return V;
  }
    break;
  case Instruction::FAdd: {
    Value* V = Builder->CreateFAdd( get_vector_version( operands.at(0) ) ,
				    get_vector_version( operands.at(1) ) );
    scalar_vector_pairs.push_back( std::make_pair( I , V ) );
    DEBUG(dbgs() << "vec add created " << *V << "\n");
    return V;
  }
    break;
  case Instruction::FSub: {
    Value* V = Builder->CreateFSub( get_vector_version( operands.at(0) ) ,
				    get_vector_version( operands.at(1) ) );
    scalar_vector_pairs.push_back( std::make_pair( I , V ) );
    DEBUG(dbgs() << "vec sub created " << *V << "\n");
    return V;
  }
    break;
  default:
    assert( 0 && "opcode not found!" );
    return NULL;
  }

  assert( 0 && "strange!" );
  return NULL;
}






void qdp_jit_vec::move_inst_before(Instruction* to_move,Instruction* before)
{
  to_move->removeFromParent();
  to_move->insertBefore(before);

  for (Use& U : to_move->operands()) {
    Value* Op = U.get();
    if (Instruction* I = dyn_cast<Instruction>(Op)) {
      I->removeFromParent();
      I->insertBefore(to_move);
    }
  }
}


Instruction* qdp_jit_vec::clone_with_operands(Instruction* to_clone,Instruction* insert_point)
{
  Instruction* Icl = to_clone->clone();
  Icl->insertBefore(insert_point);
  
  int i=0;
  for (Use& U : to_clone->operands()) {
    Value* Op = U.get();
    if (Instruction* I = dyn_cast<Instruction>(Op)) {
      Icl->setOperand( i , clone_with_operands( I , Icl ) );
    }
    i++;
  }
  return Icl;
}


Instruction* qdp_jit_vec::clone_with_operands(Instruction* to_clone)
{
  Instruction* Icl = to_clone->clone();
  Builder->Insert(Icl);
  
  int i=0;
  for (Use& U : to_clone->operands()) {
    Value* Op = U.get();
    if (Instruction* I = dyn_cast<Instruction>(Op)) {
      Icl->setOperand( i , clone_with_operands( I , Icl ) );
    }
    i++;
  }
  return Icl;
}



int qdp_jit_vec::vectorize_loads( std::vector<std::vector<Instruction*> >& load_instructions )
{
  DEBUG(dbgs() << "Vectorize loads, total of " << load_instructions.size() << "\n");

  //std::vector<std::pair<Value*,Value*> > scalar_vector_loads;
  scalar_vector_pairs.clear();

  if (load_instructions.empty())
    return 0;
  int vec_len = load_instructions.at(0).size();
  int load_vec_elem = 0;
  for( std::vector<Instruction*>& VI : load_instructions ) {
    DEBUG(dbgs() << "Processing vector of loads number " << load_vec_elem++ << "\n");
    int loads_consec = true;
    uint64_t lo,hi;
    bool first = true;
    for( Instruction* I : VI ) {
      GetElementPtrInst* GEP;
      if ((GEP = dyn_cast<GetElementPtrInst>(I->getOperand(0)))) {
	if (first) {
	  ConstantInt * CI;
	  if ((CI = dyn_cast<ConstantInt>(GEP->getOperand(1)))) {
	    lo = CI->getZExtValue();
	    hi = lo+1;
	    first=false;
	  } else {
	    DEBUG(dbgs() << "First load in the chain: Operand of GEP not a ConstantInt" << *GEP->getOperand(1) << "\n");
	    assert( 0 && "First load in the chain: Operand of GEP not a ConstantInt\n");
	    exit(0);
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
	assert( 0 && "Operand of load not a GEP" );
	exit(0);
	loads_consec = false;
      }
    }
    if (loads_consec) {
      DEBUG(dbgs() << "Loads consecuetive\n");

      LoadInst* LI = cast<LoadInst>(VI.at(0));
      GetElementPtrInst* GEP = cast<GetElementPtrInst>(LI->getOperand(0));
      Instruction* GEPcl = clone_with_operands(GEP);
      unsigned AS = LI->getPointerAddressSpace();
      VectorType *VecTy = VectorType::get( LI->getType() , vec_len );

      //Builder->SetInsertPoint( GEP );
      Value *VecPtr = Builder->CreateBitCast(GEPcl,VecTy->getPointerTo(AS));
      Value *VecLoad = Builder->CreateLoad( VecPtr );

      //DEBUG(dbgs() << "created vector load: " << *VecLoad << "\n");
      //function->dump();

      // unsigned AS = LI->getPointerAddressSpace();
      // VectorType *VecTy = VectorType::get( LI->getType() , vec_len );
      // Builder->SetInsertPoint( LI );
      // Value *VecPtr = Builder->CreateBitCast(LI->getPointerOperand(),VecTy->getPointerTo(AS));
      // Value *VecLoad = Builder->CreateLoad( VecPtr );

      scalar_vector_pairs.push_back( std::make_pair( VI.at(0) , VecLoad ) );
    } else {
      DEBUG(dbgs() << "Loads not consecutive:\n");
      for (Value* V: VI) {
	DEBUG(dbgs() << *V << "\n");
      }

      //Instruction* I = dyn_cast<Instruction>(VI.back()->getNextNode());
      //DEBUG(dbgs() << *I << "\n");

      //Builder->SetInsertPoint( VI.at(0) );


      std::vector<Instruction*> VIcl;
      for( Instruction* I : VI ) {
	VIcl.push_back( clone_with_operands(I) );
      }

      VectorType *VecTy = VectorType::get( VI.at(0)->getType() , vec_len );
      Value *Vec = UndefValue::get(VecTy);

      int i=0;
      for( Instruction* I : VIcl ) {
	Vec = Builder->CreateInsertElement(Vec, I, Builder->getInt32(i++));
      }

      scalar_vector_pairs.push_back( std::make_pair( VI.at(0) , Vec ) );      
    }
  }

  //vectorize_all_uses( scalar_vector_loads );

  DEBUG(dbgs() << "Searching for the stores:\n");
  //function->dump();

  //
  // Vectorize all StoreInst reachable by the first load of each vector of loads
  //
  {
    SetVector<Instruction*> to_visit;
    SetVector<Instruction*> stores_processed;
    for( std::vector<Instruction*>& VI : load_instructions ) {
      to_visit.insert(VI.at(0));
    }
    while (!to_visit.empty()) {
      Instruction* I = to_visit.back();
      to_visit.pop_back();
      DEBUG(dbgs() << "visiting " << *I << "\n");
      if (StoreInst* SI = dyn_cast<StoreInst>(I)) {
	if (!stores_processed.count(SI)) {
	  get_vector_version( SI );
	  stores_processed.insert( SI );
	}
      } else {
	for (Use &U : I->uses()) {
	  Value* V = U.getUser();
	  to_visit.insert(cast<Instruction>(V));
	}
      }
    }
  }

  // DEBUG(dbgs() << "After vectorizing the stores\n");
  // function->dump();

  //
  // Mark all stores as being processed
  //
  SetVector<Instruction*> to_visit;
  for( std::vector<Instruction*>& VI : load_instructions ) {
    for( Instruction* I : VI ) {
      to_visit.insert(I);
      if (GetElementPtrInst* GEP = dyn_cast<GetElementPtrInst>(I->getOperand(0))) {
	for_erasure.insert(GEP);
      }
    }
  }
  while (!to_visit.empty()) {
    Instruction* I = to_visit.back();
    to_visit.pop_back();
    for_erasure.insert(I);
    if (StoreInst* SI = dyn_cast<StoreInst>(I)) {
      stores_processed.insert(SI);
      if (GetElementPtrInst* GEP = dyn_cast<GetElementPtrInst>(SI->getOperand(1))) {
	for_erasure.insert(GEP);
      }
    } else {
      for (Use &U : I->uses()) {
	Value* V = U.getUser();
	to_visit.insert(cast<Instruction>(V));
      }
    }
  }
  
  DEBUG(dbgs() << "----------------------------------------\n");
  DEBUG(dbgs() << "After vectorize_loads\n");
  //function->dump();

  return 0;
}




void qdp_jit_vec::mark_for_erasure_all_operands(Value* V)
{
  SetVector<Value*> to_visit;

  to_visit.insert(V);

  while (!to_visit.empty()) {
    Value* v = to_visit.back();
    to_visit.pop_back();
    Instruction* vi;
    if ((vi = dyn_cast<Instruction>(v))) {
      DEBUG(dbgs() << "Found instruction " << *vi << "\n");
      for_erasure.insert(v);
      for (Use& U : vi->operands()) {
	to_visit.insert(U.get());
      }
    }
  }
}



void qdp_jit_vec::vectorize( reductions_iterator red )
{
  int vec_len = red->hi - red->lo;

  std::vector<std::vector<Instruction*> > load_instructions;

  //SetVector<Value*> to_erase;
  std::vector<SetVector<Value*> > visit(vec_len);
  int i=0;
  for ( StoreInst* SI : red->instructions ) {
    //if (i>0)
    //to_erase.insert(SI);
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
     vectorize_loads( load_instructions );
     DEBUG(dbgs() << "vectorization successful on set of " << load_instructions.size() << " load sets\n");
  }
}



void qdp_jit_vec::track( StoreInst* SI , int64_t offset )
{
  //DEBUG(dbgs() << ">>>>> track " << *SI << " " << offset << "\n");

  if (stores_processed.count(SI)) {
    DEBUG(dbgs() << ">>>>> track " << *SI << " " << offset << "  (already processed)\n");
    return;
  } else {
    DEBUG(dbgs() << ">>>>> track " << *SI << " " << offset << "\n");
  }


  if (reductions.empty()) {
    DEBUG(dbgs() << "set of reductions empty, will create a new one.\n");
    reduction r(SI,offset);
    reductions.push_back(r);
    return;
  }

  reductions_iterator red_match;
  bool found_vectorization = false;
  bool found_reduction = false;
  for (reductions_iterator r = reductions.begin() ; r != reductions.end() ; ++r ) {
    if ( r->hi == offset ) {
      found_reduction = true;
      r->instructions.push_back( SI );
      r->hi++;
      if (r->hi - r->lo == vector_length) {
	DEBUG(dbgs() << "Found vectorization! lo=" << r->lo << " hi=" << r->hi << "\n");
	red_match = r;
	found_vectorization = true;
	break;
      }
    }
  }

  if (found_vectorization) {
    DEBUG(dbgs() << "Do vectorization..." << "\n");
    vectorize( red_match );

    DEBUG(dbgs() << "Remove reduction..." << "\n");
    reductions.erase( red_match );
  } else if (!found_reduction) {
    DEBUG(dbgs() << "none of the reductions matches, will create a new one.\n");
    reduction r(SI,offset);
    reductions.push_back(r);
  }
}


void sort_stores(BasicBlock* BB)
{
  std::vector< std::pair< uint64_t , StoreInst* > > stores;
  Instruction* Ret;

  for (Instruction& I : *BB) {
    if (StoreInst* SI = dyn_cast<StoreInst>(&I)) {
      Value* V = SI->getOperand(1);
      if (GetElementPtrInst* GEP = dyn_cast<GetElementPtrInst>(V)) {
	//DEBUG(dbgs() << "Found GEP " << *GEP << "\n");
	if (ConstantInt * CI = dyn_cast<ConstantInt>(GEP->getOperand(1))) {
	  uint64_t off = CI->getZExtValue();
	  stores.push_back( std::make_pair(off,SI) );
	}
      }
    }
    if (ReturnInst* RI = dyn_cast<ReturnInst>(&I)) {
      Ret = RI;
    }
  }

  DEBUG(dbgs() << "Sorting " << stores.size() << " stores according to their offset\n");
  std::sort(stores.begin(), stores.end(), 
	    [](const std::pair<uint64_t , StoreInst*> &left, 
	       const std::pair<uint64_t , StoreInst*> &right) {
    return left.first < right.first;
	    });
  DEBUG(dbgs() << "done sorting!\n");

  for ( std::pair<uint64_t , StoreInst*>& p : stores ) {
    p.second->removeFromParent();
    p.second->insertBefore(Ret);
  }

  //BB->dump();
}



bool qdp_jit_vec::runOnFunction(Function &F) {
  //DEBUG(dbgs() << "qdp_jit_vec running on Function " << F << "\n");
  //dbgs() << "qdp_jit_vec running on Function " << F << "\n";
  //module = &M;
  IRBuilder<true, TargetFolder> TheBuilder(F.getContext(), TargetFolder(DL));
  Builder = &TheBuilder;

  BasicBlock& BB = F.getEntryBlock();
  function = &F;
  orig_BB = &BB;


  sort_stores(orig_BB);


  vec_BB = llvm::BasicBlock::Create(llvm::getGlobalContext(), "vectorized" );
  function->getBasicBlockList().push_front(vec_BB);

  Builder->SetInsertPoint(vec_BB);

  for (Instruction& I : BB) {
    if (StoreInst* SI = dyn_cast<StoreInst>(&I)) {
      Value* V = SI->getOperand(1);
      if (GetElementPtrInst* GEP = dyn_cast<GetElementPtrInst>(V)) {
	//DEBUG(dbgs() << "Found GEP " << *GEP << "\n");
	if (ConstantInt * CI = dyn_cast<ConstantInt>(GEP->getOperand(1))) {
	  int64_t off = CI->getZExtValue();
	  //DEBUG(dbgs() << " number = " << off << "\n");
	  track( SI , off );
	} else {
	  assert( 0 && "first operand of GEP is not a constant" );
	}
      } else {
	assert( 0 && "first operand of store instr is not an GEP" );
      }
    }
  }


  Builder->CreateBr(orig_BB);

  //function->dump();

#if 1
  DEBUG(dbgs() << "Erasing instruction count = " << for_erasure.size() << "\n");
  for ( Value* v: for_erasure ) {
    if (Instruction *Inst = dyn_cast<Instruction>(v)) {
      DEBUG(dbgs() << "erasure: " << *Inst << "\n");
      if (!Inst->use_empty())
	Inst->replaceAllUsesWith(UndefValue::get(Inst->getType()));
      Inst->eraseFromParent();
    }
  }
#endif


  DEBUG(dbgs() << "Unprocessed reductions left = " << reductions.size() << "\n");
  int i = 0;
  for (reductions_iterator r = reductions.begin() ; r != reductions.end() ; ++r ) {
    DEBUG(dbgs() << "------------ reduction " << i++ << "\n");
    for (Value* V: r->instructions) {
      DEBUG(dbgs() << *V << "\n");
    }
  }

  //function->dump();

  return true;
}


char qdp_jit_vec::ID = 0;
static RegisterPass<qdp_jit_vec> X(SV_NAME, "QDP-JIT vectorize code");


FunctionPass *llvm::create_qdp_jit_vec_pass() {
  return new qdp_jit_vec();
}



//INITIALIZE_PASS_BEGIN(qdp_jit_vec, "qdp-jit-roll", "QDP-JIT roll code into a new loop", false, false)
//INITIALIZE_AG_DEPENDENCY(AliasAnalysis)
//INITIALIZE_PASS_END(qdp_jit_vec, "qdp-jit-roll", "QDP-JIT roll code into a new loop", false, false)

