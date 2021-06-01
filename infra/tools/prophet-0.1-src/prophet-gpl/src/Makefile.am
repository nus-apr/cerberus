AM_CXXFLAGS = -fopenmp `llvm-config --cxxflags` -Werror -Wall -Wno-unknown-pragmas -fno-strict-aliasing

bin_PROGRAMS = pdiffer prophet learner playground

lib_LTLIBRARIES = libprofiler.la libprofile_runtime.la libtest_runtime.la

ClangLDADD = -lclangTooling -lclangFrontendTool -lclangFrontend -lclangDriver -lclangSerialization -lclangCodeGen \
			 -lclangParse -lclangSema -lclangStaticAnalyzerFrontend -lclangStaticAnalyzerCheckers \
			 -lclangStaticAnalyzerCore -lclangAnalysis -lclangIndex -lclangARCMigrate -lclangEdit \
			 -lclangAST -lclangLex -lclangBasic
ClangLDADD += -lLLVMLTO -lLLVMObjCARCOpts -lLLVMLinker -lLLVMBitWriter -lLLVMIRReader -lLLVMAsmParser -lLLVMR600CodeGen \
			  -lLLVMipo -lLLVMVectorize -lLLVMR600AsmParser -lLLVMR600Desc -lLLVMR600Info -lLLVMR600AsmPrinter \
			  -lLLVMSystemZDisassembler -lLLVMSystemZCodeGen -lLLVMSystemZAsmParser -lLLVMSystemZDesc -lLLVMSystemZInfo \
			  -lLLVMSystemZAsmPrinter -lLLVMHexagonDisassembler -lLLVMHexagonCodeGen -lLLVMHexagonDesc -lLLVMHexagonInfo \
			  -lLLVMNVPTXCodeGen -lLLVMNVPTXDesc -lLLVMNVPTXInfo -lLLVMNVPTXAsmPrinter -lLLVMCppBackendCodeGen \
			  -lLLVMCppBackendInfo -lLLVMMSP430CodeGen -lLLVMMSP430Desc -lLLVMMSP430Info -lLLVMMSP430AsmPrinter \
			  -lLLVMXCoreDisassembler -lLLVMXCoreCodeGen -lLLVMXCoreDesc -lLLVMXCoreInfo -lLLVMXCoreAsmPrinter \
			  -lLLVMMipsDisassembler -lLLVMMipsCodeGen -lLLVMMipsAsmParser -lLLVMMipsDesc -lLLVMMipsInfo \
			  -lLLVMMipsAsmPrinter -lLLVMAArch64Disassembler -lLLVMAArch64CodeGen -lLLVMAArch64AsmParser \
			  -lLLVMAArch64Desc -lLLVMAArch64Info -lLLVMAArch64AsmPrinter -lLLVMAArch64Utils -lLLVMARMDisassembler \
			  -lLLVMARMCodeGen -lLLVMARMAsmParser -lLLVMARMDesc -lLLVMARMInfo -lLLVMARMAsmPrinter \
			  -lLLVMPowerPCDisassembler -lLLVMPowerPCCodeGen -lLLVMPowerPCAsmParser -lLLVMPowerPCDesc -lLLVMPowerPCInfo \
			  -lLLVMPowerPCAsmPrinter -lLLVMSparcDisassembler -lLLVMSparcCodeGen -lLLVMSparcAsmParser -lLLVMSparcDesc \
			  -lLLVMSparcInfo -lLLVMSparcAsmPrinter -lLLVMTableGen -lLLVMDebugInfo -lLLVMOption -lLLVMX86Disassembler \
			  -lLLVMX86AsmParser -lLLVMX86CodeGen -lLLVMSelectionDAG -lLLVMAsmPrinter -lLLVMX86Desc \
			  -lLLVMMCDisassembler -lLLVMX86Info -lLLVMX86AsmPrinter -lLLVMX86Utils -lLLVMMCJIT -lLLVMLineEditor \
			  -lLLVMInstrumentation -lLLVMInterpreter -lLLVMExecutionEngine -lLLVMRuntimeDyld -lLLVMCodeGen \
			  -lLLVMScalarOpts -lLLVMProfileData -lLLVMObject -lLLVMMCParser -lLLVMBitReader -lLLVMInstCombine \
			  -lLLVMTransformUtils -lLLVMipa -lLLVMAnalysis -lLLVMTarget -lLLVMMC -lLLVMCore -lLLVMSupport \
			  -ltinfo -lz -lpthread -lrt -ldl -lm


pdiffer_SOURCES = pdiffer.cpp Utils.cpp ASTDiffer.cpp SourceContextManager.cpp LocalAnalyzer.cpp \
				  GlobalAnalyzer.cpp ASTUtils.cpp BenchProgram.cpp RepairCandidateGenerator.cpp \
				  CodeRewrite.cpp FeatureExtract.cpp
pdiffer_LDFLAGS = `llvm-config --ldflags`
pdiffer_LDADD = $(ClangLDADD) -lexplain

learner_SOURCES = learner.cpp FeatureExtract.cpp SourceContextManager.cpp LocalAnalyzer.cpp \
				  GlobalAnalyzer.cpp ASTUtils.cpp BenchProgram.cpp RepairCandidateGenerator.cpp \
				  Utils.cpp CodeRewrite.cpp
learner_LDFLAGS = `llvm-config --ldflags`
learner_LDADD = $(ClangLDADD) -lexplain

prophet_SOURCES = Main.cpp Utils.cpp RepairSearchEngine.cpp BenchProgram.cpp ASTUtils.cpp \
				  ErrorLocalizer.cpp LocalAnalyzer.cpp ProfileErrorLocalizer.cpp SourceContextManager.cpp \
				  GlobalAnalyzer.cpp DuplicateDetector.cpp ExprSynthesizer.cpp RepairCandidateGenerator.cpp \
				  CodeRewrite.cpp FeatureExtract.cpp
prophet_LDFLAGS = `llvm-config --ldflags`
prophet_LDADD = $(ClangLDADD) -lexplain

playground_SOURCES = PlayGround.cpp Utils.cpp BenchProgram.cpp
playground_LDFLAGS = `llvm-config --ldflags`
playground_LDADD = $(ClangLDADD) -lexplain

libprofiler_la_SOURCES = ProfilerAction.cpp
libprofiler_la_LDFLAGS = `llvm-config --ldflags`
libprofiler_la_LIBADD = -lLLVMSupport

libprofile_runtime_la_SOURCES = _prophet_profile.cpp
libprofile_runtime_la_LIBADD = -lpthread

libtest_runtime_la_SOURCES = _test_runtime.cpp
