/*
 * File: CSE_Cpp.cpp
 *
 * Description:
 *   This is where you implement the C++ version of project 4 support.
 */

/* LLVM Header Files */
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Type.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/IR/Dominators.h"
#include "llvm/ADT/GraphTraits.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/IR/ValueMap.h"
#include "llvm/Support/GraphWriter.h"
#include "llvm/IR/InstIterator.h"

#include <map>
#include <iostream>
#include <stdio.h>
#include <string.h>
using namespace llvm;
using namespace std;


#include "CSE.h"
#include "dominance.h"
#include "transform.h"
#include "worklist.h"
#include "cfg.h"
#include "llvm-c/Core.h"

int CSEDead=0;
int CSEElim=0;
int CSESimplify=0;
int CSELdElim=0;
int CSELdStElim=0;
int CSERStElim=0;
int total_deleted_instr=0;
//////////////////////////////////////////////////////DEAD CODE ELIMINATION////////////////////////////////////////////////////////////////////////////////////////////
int isDead(Instruction &I)
{
  int opcode = I.getOpcode();
  switch(opcode){
  case Instruction::Add:
  case Instruction::FNeg:
  case Instruction::FAdd: 	
  case Instruction::Sub:
  case Instruction::FSub: 	
  case Instruction::Mul:
  case Instruction::FMul: 	
  case Instruction::UDiv:	
  case Instruction::SDiv:	
  case Instruction::FDiv:	
  case Instruction::URem: 	
  case Instruction::SRem: 	
  case Instruction::FRem: 	
  case Instruction::Shl: 	
  case Instruction::LShr: 	
  case Instruction::AShr: 	
  case Instruction::And: 	
  case Instruction::Or: 	
  case Instruction::Xor: 	
  case Instruction::Alloca:
  case Instruction::GetElementPtr: 	
  case Instruction::Trunc: 	
  case Instruction::ZExt: 	
  case Instruction::SExt: 	
  case Instruction::FPToUI: 	
  case Instruction::FPToSI: 	
  case Instruction::UIToFP: 	
  case Instruction::SIToFP: 	
  case Instruction::FPTrunc: 	
  case Instruction::FPExt: 	
  case Instruction::PtrToInt: 	
  case Instruction::IntToPtr: 	
  case Instruction::BitCast: 	
  case Instruction::AddrSpaceCast: 	
  case Instruction::ICmp: 	
  case Instruction::FCmp: 	
  case Instruction::PHI: 
  case Instruction::Select: 
  case Instruction::ExtractElement: 	
  case Instruction::InsertElement: 	
  case Instruction::ShuffleVector: 	
  case Instruction::ExtractValue: 	
  case Instruction::InsertValue: 
    if ( I.use_begin() == I.use_end() )
      {
	return true;
      }    
    break;

  case Instruction::Load:
    {
      LoadInst *li = dyn_cast<LoadInst>(&I);
      if (li->isVolatile())
	return false;

      if ( I.use_begin() == I.use_end() )
	{
	  return true;
	}
      
      break;
    }
  
  default: // any other opcode fails (includes stores and branches)
    // we don't know about this case, so conservatively fail!
    return false;
  }
  
  return false;
}

void DCE_pass(Module &M)
{
  /////optimization zero//////////////////
  for(auto f = M.begin(); f!=M.end(); f++)       // loop over functions
  {
    std::set<Instruction*> worklist;
    for(auto bb= f->begin(); bb!=f->end(); bb++)
	  {
	  // loop over basic blocks
	    for(auto i = bb->begin(); i != bb->end(); i++)
	    {
	      //loop over instructions
	      if (isDead(*i)) 
        {
		      //add I to a worklist to replace later
		      worklist.insert(&*i);
        }
	    }
	  }

    while(worklist.size()>0) 
	  {
	    // Get the first item 
	    Instruction *i = *(worklist.begin());
	    // Erase it from worklist
	    worklist.erase(i);
	  
	    //if(isDead(*i))
	    //{
	      i->eraseFromParent();
	      CSEDead++;
        total_deleted_instr++;
	    //}
	  
	  }
  }
}
/////////////////////////////////////////////////////////CONSTANT FOLDING////////////////////////////////////////////////////////////////////////////////////////
void ConstantFolding(Module &M)
{
  //////optimization one///////////
  for(auto f = M.begin(); f!=M.end(); f++)
  {
    std::set<Instruction*> worklist;
    for(auto bb= f->begin(); bb!=f->end(); bb++)
    {
      for(auto i = bb->begin(); i != bb->end();i++)
      {
        Value* v = unwrap(InstructionSimplify(wrap(&*i)));
        if(v != NULL)
        {
          CSESimplify++;
          total_deleted_instr++;
          i->replaceAllUsesWith(v);
          worklist.insert(&*i);
        }
      }
    }

    while(worklist.size()>0) 
	  {
	    // Get the first item 
	    Instruction *i = *(worklist.begin());
	    // Erase it from worklist
	    worklist.erase(i);
	    i->eraseFromParent(); 
	  }

  }
}
////////////////////////////////////////////////////////BASIC COMMOM SUBEXPRESSION ELIMINATION/////////////////////////////////////////////////////////////////////////////////////////////
void CSE_Basic_processing(BasicBlock* BB, Instruction* I, bool flag)
{
  if(( isa<LoadInst>(I)       
    || isa<StoreInst>(I)       
    || I->isTerminator() 
    || isa<VAArgInst>(I)      
    || isa<CallInst>(I)       
    || isa<AllocaInst>(I)      
    || isa<FCmpInst>(I) 
    || isa<llvm::BranchInst>(I)))
  {
    return;
  }
  else
  {
    if(flag==1)
    {
      BasicBlock* childBB;
      for (childBB = unwrap(LLVMFirstDomChild(wrap(BB)));childBB != NULL;childBB = unwrap(LLVMNextDomChild(wrap(BB),wrap(childBB))))
      {
		std::set<Instruction*> worklist;
        for(auto i = childBB->begin(); i != childBB->end();i++)
        {
          if(I->isIdenticalTo(&*i))
          {
            CSEElim++;
            total_deleted_instr++;
            i->replaceAllUsesWith(I);
            worklist.insert(&*i);
          }
        }
		while(worklist.size()>0) 
	      {
	        // Get the first item 
	        Instruction *inst = *(worklist.begin());
	        // Erase it from worklist
	        worklist.erase(inst);
	        inst->eraseFromParent(); 
	      }
        CSE_Basic_processing(&*childBB,&*I,1);
      }
    }
    else
    {
      Instruction* next_instr = I->getNextNonDebugInstruction();
	  std::set<Instruction*> worklist;
      while(next_instr != NULL)
      {
        if(I->isIdenticalTo(next_instr))
        {
          CSEElim++;
          total_deleted_instr++;
          next_instr->replaceAllUsesWith(I);
		  worklist.insert(next_instr);
        }
        next_instr = next_instr->getNextNonDebugInstruction();
      }
	  while(worklist.size()>0) 
	    {
	        // Get the first item 
	        Instruction *inst = *(worklist.begin());
	        // Erase it from worklist
	        worklist.erase(inst);
	        inst->eraseFromParent(); 
	    }
      CSE_Basic_processing(&*BB,&*I,1);
    }
  }
}

void CSE_Basic_Pass(Module &M)
{
  /////////optimization one///////////////
  for(auto f = M.begin(); f!=M.end(); f++)
  {
    for(auto bb = f->begin(); bb!=f->end(); bb++)
    {
      for(auto i = bb->begin(); i != bb->end();i++)
      {
        CSE_Basic_processing(&*bb,&*i,0);
      }
    }
  }
}
////////////////////////////////////////////////////LOAD ELIMINATION////////////////////////////////////////////////////////////////////////////////////////////////////////
bool Load_Elim_processing(Instruction* L, Instruction* R)
{
  LoadInst *li = dyn_cast<LoadInst>(R);
  if((li != NULL) && 
    (!(li->isVolatile())) && 
    (L->getType() == R->getType()) &&
	(((LoadInst*)L)->getPointerOperand() == ((LoadInst*)R)->getPointerOperand()))
    {
      return true;
    }
    else
    {
      return false;
    }       
}

void LoadElim_Pass(Module &M)
{
  for(auto f = M.begin(); f!=M.end(); f++)
  {
	std::set<Instruction*> worklist;
    for(auto bb = f->begin(); bb!=f->end(); bb++)
    {
      for(auto i = bb->begin(); i != bb->end();i++)
      {
        Instruction* next_instr = i->getNextNonDebugInstruction();
        if(isa<LoadInst>(&*i))
        {
            while(next_instr != NULL)
            {
              if(isa<StoreInst>(next_instr) || isa<CallInst>(next_instr))
              {
                break;
              }
              else
              {
                if(Load_Elim_processing(&*i,next_instr))
                {
                  CSELdElim++;
                  total_deleted_instr++;
                  next_instr->replaceAllUsesWith(&*i);
			      worklist.insert(next_instr);
                }
              }
              next_instr = next_instr->getNextNonDebugInstruction();
	          while(worklist.size()>0) 
              {
	            // Get the first item 
	            Instruction *inst = *(worklist.begin());
	            // Erase it from worklist
	            worklist.erase(inst);
	            inst->eraseFromParent(); 
	          }
            }
        }
      }
    }
  }
}
////////////////////////////////////////////////LOAD-STORE ELIMINATION///////////////////////////////////////////////////////////////////////////////////////////////////////////
void LdSt_Elim(Module &M)
{
  for(auto f = M.begin(); f!=M.end(); f++)
  {
    for(auto bb = f->begin(); bb!=f->end(); bb++)
    {
    for(auto i = bb->begin(); i != bb->end();i++)
      {
        if(isa<StoreInst>(*i))
        {
          auto next_instr=i;
          for(++next_instr;next_instr!=bb->end();)
          {            
            if((isa<LoadInst>(*next_instr)) && !(dyn_cast<LoadInst>(next_instr)->isVolatile()) && (*i).getOperand(0)->getType() == next_instr->getType() && (*i).getOperand(1) == next_instr->getOperand(0))
            {
              CSELdStElim++;
              total_deleted_instr++;
              next_instr->replaceAllUsesWith(i->getOperand(0));
              next_instr = next_instr->eraseFromParent();
            }
            else if((isa<StoreInst>(*next_instr)) && !(dyn_cast<StoreInst>(i)->isVolatile()) && ((*i).getOperand(0)->getType() == next_instr->getOperand(0)->getType()) && (*i).getOperand(1) == next_instr->getOperand(1))
            {
              CSERStElim++;
              total_deleted_instr++;
              i=i->eraseFromParent();
            }
            if(isa<StoreInst>(*next_instr) || isa<LoadInst>(*next_instr) || isa<CallInst>(*next_instr))
            {
              break;
            }
            else
            {
              next_instr++;              
            }     
          }
        }
      }
    }
  }
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
void LLVMCommonSubexpressionElimination_Cpp(Module *M)
{
  DCE_pass(*M);
  ConstantFolding(*M);
  CSE_Basic_Pass(*M);
  LoadElim_Pass(*M);
  LdSt_Elim(*M);

//   print out summary of results
  fprintf(stderr,"CSE_Dead.....%d\n",  CSEDead);
  fprintf(stderr,"CSE_Basic.....%d\n", CSEElim);
  fprintf(stderr,"CSE_Simplify..%d\n", CSESimplify);
  fprintf(stderr,"CSE_RLd.......%d\n", CSELdElim);
  fprintf(stderr,"CSE_RSt.......%d\n", CSERStElim);
  fprintf(stderr,"CSE_LdSt......%d\n", CSELdStElim);
  fprintf(stderr,"Total Instructions Deleted: %d\n",total_deleted_instr); 
  DCE_pass(*M);
  ConstantFolding(*M);
  CSE_Basic_Pass(*M);
  
  fprintf(stderr,"CSE_Dead(after modification).....%d\n",  CSEDead);
  fprintf(stderr,"CSE_Basic(after modification).....%d\n", CSEElim);
  fprintf(stderr,"CSE_Simplify(after modification)..%d\n", CSESimplify);
  fprintf(stderr,"CSE_RLd(after modification).......%d\n", CSELdElim);
  fprintf(stderr,"CSE_RSt(after modification).......%d\n", CSERStElim);
  fprintf(stderr,"CSE_LdSt(after modification)......%d\n", CSELdStElim);
  fprintf(stderr,"Total Instructions Deleted(after modification): %d\n",total_deleted_instr); 
}

