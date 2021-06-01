// Copyright (C) 2016 Fan Long, Martin Rianrd and MIT CSAIL 
// Prophet
// 
// This file is part of Prophet.
// 
// Prophet is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
// 
// Prophet is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
// 
// You should have received a copy of the GNU General Public License
// along with Prophet.  If not, see <http://www.gnu.org/licenses/>.
#include "Utils.h"
#include "BenchProgram.h"
#include "ErrorLocalizer.h"
#include "ProfileErrorLocalizer.h"
#include "RepairSearchEngine.h"
#include "FeatureVector.h"
#include "FeatureParameter.h"
#include "ConfigFile.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Decl.h"
#include "llvm/Support/CommandLine.h"
#include <iostream>
#include <string>
#include <cstdlib>
#include <set>
#include <vector>
#include <algorithm>
#include <stdio.h>
#include <fstream>
#include <sstream>
#include <unistd.h>

llvm::cl::opt<std::string> LogFileName("log", llvm::cl::value_desc("log-filename"), llvm::cl::init("repair.log"),
        llvm::cl::desc("Specify the logfile for this run!"));
llvm::cl::opt<unsigned int> VerboseLevel("vl", llvm::cl::value_desc("verbose-level"), llvm::cl::init(2),
        llvm::cl::desc("How many info will output to screen 0-10(0min-10max)."));
llvm::cl::opt<unsigned int> LogLevel("ll", llvm::cl::value_desc("log-level"), llvm::cl::init(2),
        llvm::cl::desc("How many info will output to log 0-10(0min-10max)."));
llvm::cl::opt<std::string> ConfigFilename(llvm::cl::Positional,
        llvm::cl::desc("Specify the configure filename"), llvm::cl::value_desc("conf-filename"));
llvm::cl::opt<std::string> RunWorkDir("r",
        llvm::cl::desc("Run with particular work dir, if it exists, it will resume the execution."),
        llvm::cl::value_desc("workdir"));
llvm::cl::opt<bool> SkipProfileBuild("skip-profile-build", llvm::cl::desc("Skip To Build Profiler"));
llvm::cl::opt<bool> NoCleanUp("no-clean-up",
        llvm::cl::desc("Do not clean work dir after finish"));
llvm::cl::opt<bool> InitOnly("init-only",
        llvm::cl::desc("Just initialize the work directory verify + localization!"));
llvm::cl::opt<bool> SkipVerify("skip-verify",
        llvm::cl::desc("Skip verify the work directory with test cases!"));
llvm::cl::opt<std::string> PrintFixOnly("print-fix-only",
        llvm::cl::desc("Do not test and generate repair, print all fix candidates only"),
        llvm::cl::value_desc("output-file"));
llvm::cl::opt<bool> NaiveRepair("naive",
        llvm::cl::desc("Run naive repair that only inserts return/ delete statements/branches!"));
llvm::cl::opt<std::string> PrintLocalizationOnly("print-loc-only",
        llvm::cl::desc("Only run error localization and print candidate locations"),
        llvm::cl::value_desc("output-file"));
llvm::cl::opt<int> TryAtLeast("try-at-least",
        llvm::cl::desc("The number of mutations we try before we terminate."));
llvm::cl::opt<bool> FullExplore("full-explore",
        llvm::cl::desc("Terminate only when we tried everything in the search space."));
llvm::cl::opt<bool> FullSynthesis("full-synthesis",
        llvm::cl::desc("Try all conditions instead of choosing the first one."));
llvm::cl::opt<std::string> SummaryFile("summary-file", llvm::cl::init(""),
        llvm::cl::desc("Output the list of generated patch id and scores to the file, sorted!"));
llvm::cl::opt<bool> ConsiderAll("consider-all",
        llvm::cl::desc("Consider all possible files."));
llvm::cl::opt<unsigned int> FirstNLoc("first-n-loc", llvm::cl::init(5000),
        llvm::cl::desc("Consider first n location, default 5000."));
llvm::cl::opt<std::string> ParameterFile("feature-para", llvm::cl::value_desc("feature-parameter-file"),
        llvm::cl::init(""), llvm::cl::desc("Specify the feature parameter file. Disable learning if not specified."));
llvm::cl::opt<bool> NoFeature("no-feature", llvm::cl::value_desc("just-use-localization-distribution"),
        llvm::cl::init(false), llvm::cl::desc("Rank candidates with only localization distribution!"));
llvm::cl::opt<bool> Random("random", llvm::cl::init(false), llvm::cl::desc("Just use random search over the space."));
llvm::cl::opt<double> GeoP("geop", llvm::cl::value_desc("flip probability"),
        llvm::cl::init(0.02), llvm::cl::desc("Flip Probability of Geometric Computations!"));
llvm::cl::opt<unsigned int> Timeout("timeout", llvm::cl::init(0), llvm::cl::desc("Soft timeout limit in hours"));
llvm::cl::opt<bool> ForCPP("cpp", llvm::cl::init(false));

int main(int argc, char* argv[]) {
    llvm::cl::ParseCommandLineOptions(argc, argv);

    // Setup log file stuff
    std::string log_filename = LogFileName.getValue();
    unsigned int verbose_level = VerboseLevel.getValue();
    unsigned int log_level = LogLevel.getValue();
    outlog_open(log_filename.c_str(), verbose_level, log_level);
    reset_timer();

    std::string config_file_name = ConfigFilename.getValue();
    std::string run_work_dir = RunWorkDir.getValue();

    if ((config_file_name == "") && (run_work_dir == "")) {
        outlog_printf(0, "Must specify configuration file or existing working directory!");
        exit(1);
    }

    outlog_printf(1, "Initialize the program!\n");
    BenchProgram *P;
    if (config_file_name != "") {
        P = new BenchProgram(config_file_name, run_work_dir,
                InitOnly || NoCleanUp || (run_work_dir != ""));
        if (run_work_dir != "") {
            int ret = system((std::string("cp -f ") + config_file_name + " " + run_work_dir + "/repair.conf").c_str());
            assert( ret == 0);
        }
    }
    else
        P = new BenchProgram(run_work_dir);

    if (!SkipVerify) {
        outlog_printf(1, "Verify Test Cases\n");
        bool ret = P->verifyTestCases();
        if (!ret) {
            outlog_printf(1, "Repair error: Verification failed!\n");
            exit(1);
        }
        outlog_printf(1, "Done Verification\n");
    }

    ConfigFile *config = P->getCurrentConfig();
    std::string localizer = config->getStr("localizer");

    std::set<std::string> bugged_file = splitStringWithWhite(config->getStr("bugged_file"));

    ErrorLocalizer *L = NULL;
    if (localizer == "")
        L = new NaiveErrorLocalizer(*P);
    else if (localizer == "profile") {
        if (existFile(P->getLocalizationResultFilename()))
            L = new ProfileErrorLocalizer(*P, P->getLocalizationResultFilename());
        else if (SkipProfileBuild)
            L = new ProfileErrorLocalizer(*P, bugged_file, true);
        else
            L = new ProfileErrorLocalizer(*P, bugged_file, false);
    }

   if (InitOnly) {
        delete L;
        delete P;
        outlog_close();
        return 0;
    }

    if (PrintLocalizationOnly.getValue() != "") {
        L->printResult(PrintLocalizationOnly.getValue());
        delete L;
        delete P;
        outlog_close();
        return 0;
    }

    FeatureParameter *FP = NULL;
    bool learning = false;
    if ((ParameterFile.getValue() != "") || (NoFeature.getValue())) {
        FP = new FeatureParameter;
        if (NoFeature.getValue()) {
            FP->resetZero(FeatureVector::MAX_FEATURE);
        }
        else {
            std::ifstream fin(ParameterFile.getValue(), std::ifstream::in);
            if (fin.is_open()) {
                fin >> *FP;
                fin.close();
            }
        }
        learning = true;
    }

    RepairSearchEngine E(*P, L, NaiveRepair.getValue(), learning, FP);
    if (!ConsiderAll.getValue())
        if (bugged_file.size())
            E.setBuggedFile(bugged_file);
    E.setLocLimit(FirstNLoc.getValue());
    E.setGeoP(GeoP.getValue());
    E.setRandom(Random.getValue());
    E.setSummaryFile(SummaryFile.getValue());
    if (Timeout.getValue() != 0)
        E.setTimeoutLimit(((unsigned long long)Timeout.getValue()) * 60 * 60);

    int ret;
    bool fix_only = false;
    if (PrintFixOnly.getValue() != "")
        fix_only = true;
    std::string fixed_out_file = config->getStr("fixed_out_file");
    if (fixed_out_file == "")
        fixed_out_file = "__fixed_";
    if (fix_only)
        ret = E.run(PrintFixOnly.getValue(), 0, fix_only, false);
    else if (FullExplore)
        ret = E.run(fixed_out_file, 1000000000L, false, FullSynthesis.getValue());
    else
        ret = E.run(fixed_out_file, (size_t)TryAtLeast.getValue(), false, FullSynthesis.getValue());

    delete L;
    delete P;
    outlog_close();

    if (FP)
        delete FP;

    return ret;
}
