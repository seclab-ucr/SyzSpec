#ifndef _CALL_GRAPH_H
#define _CALL_GRAPH_H

#include "Analyzer.h"
#include "MLTA.h"
#include "Config.h"
#include <cstdint>

class CallGraphPass : 
	public virtual IterativeModulePass, public virtual MLTA {

	private:

		//
		// Variables
		//

		// Index of the module
		uint64_t MIdx;

		std::set<CallInst *>CallSet;
		std::set<CallInst *>ICallSet;
		std::set<CallInst *>MatchedICallSet;


		//
		// Methods
		//
		void doMLTA(Function *F);


	public:
		static int AnalysisPhase;

		CallGraphPass(GlobalContext *Ctx_)
			: IterativeModulePass(Ctx_, "CallGraph"),
			MLTA(Ctx_) {

				LoadElementsStructNameMap(Ctx->Modules);
				MIdx = 0;
			}

		virtual bool doInitialization(llvm::Module *);
		virtual bool doFinalization(llvm::Module *);
		virtual bool doModulePass(llvm::Module *);

};

#endif
