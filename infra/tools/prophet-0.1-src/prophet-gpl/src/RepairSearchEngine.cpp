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
#define ENABLE_DEBUG
#include "config.h"
#include "Utils.h"
#include "ASTUtils.h"
#include "ErrorLocalizer.h"
#include "RepairSearchEngine.h"
#include "SourceContextManager.h"
#include "ExprSynthesizer.h"
#include "RepairCandidateGenerator.h"
#include "llvm/Support/CommandLine.h"
#include "clang/AST/ASTContext.h"
#include "FeatureVector.h"
#include "FeatureParameter.h"
#include <stdlib.h>
#include <unistd.h>
#include <fstream>
#include <iostream>
#include <queue>

llvm::cl::opt<bool> DumpFeatureDetail("dump-feature", llvm::cl::init(false));
llvm::cl::opt<bool> PrintBlowupInfo("blowup", llvm::cl::init(false));

using namespace clang;

static std::string replaceSlash(const std::string &str) {
    std::string res = "";
    for (size_t i = 0; i < str.size(); i++)
        if (str[i] == '/')
            res.push_back('_');
        else
            res.push_back(str[i]);
    return res;
}

// FIXME: The interface is kind of shitty, we are filling rc.scoreMap
// here. We should find a better place to do this...
double computeScores(SourceContextManager &M, FeatureParameter *FP,
        FeatureExtractor &EX, RepairCandidate &rc, bool learning, bool random) {
    if (learning) {
        std::set<clang::Expr*> atoms = rc.getCandidateAtoms();
        double best = -1e+20;
        for (std::set<clang::Expr*>::iterator it = atoms.begin(); it != atoms.end(); ++it) {
            FeatureVector vec = EX.extractFeature(M, rc, *it);
            double res = FP->dotProduct(vec) + rc.score;
            // we are going to nuke the score if random is set
            if (random)
                res = rand();
            rc.scoreMap[*it] = res;
            if (res > best) best = res;
        }
        return best;
    }
    else {
        // we are going to nuke the score if random is set
        if (random)
            return rand();
        return rc.score;
    }
}

void dumpSignificantInVec(FILE* fout, FeatureParameter *FP, const FeatureVector &v, double alpha) {
    for (size_t i = 0; i < v.size(); i++)
        if ((FP->at(v[i]) < -alpha) || (FP->at(v[i]) > alpha)) {
            fprintf(fout, "--%s %lf\n", FeatureVector::fidToString(v[i]).c_str(), FP->at(v[i]));
        }
}

int RepairSearchEngine::run(const std::string &out_file, size_t try_at_least,
        bool print_fix_only, bool full_synthesis) {
    RepairCandidateQueue q;
    SourceContextManager M(P, naive);

    outlog_printf(1, "Generating repair candidates!\n");

    // Processing the localization result, collect the files that we need to
    // process if the bugged_files are not given
    std::vector<SourcePositionTy> all_locs = L->getCandidateLocations();
    std::vector<std::string> files;
    std::set<SourcePositionTy> remaining_locs;
    std::map<SourcePositionTy, size_t> loc_rank_map;
    files.clear();
    remaining_locs.clear();
    loc_rank_map.clear();
    {
        std::set<std::string> tmp;
        tmp.clear();
        for (size_t i = 0; i < all_locs.size(); i++) {
            // FIXME: Make just does not work, we turn off header for now!
            if (!is_header(all_locs[i].expFilename))
                remaining_locs.insert(M.fixSourceLocation(all_locs[i]));
            loc_rank_map.insert(std::make_pair(M.fixSourceLocation(all_locs[i]), i));
            if ((tmp.count(all_locs[i].expFilename) == 0) &&
                    (!is_header(all_locs[i].expFilename))) {
                tmp.insert(all_locs[i].expFilename);
                files.push_back(all_locs[i].expFilename);
            }
            if (remaining_locs.size() >= loc_limit)
                break;
        }
    }

    size_t candidate_cnt = 0;
    size_t partial_candidate_cnt = 0;
    FeatureExtractor EX;
    for (size_t i = 0; i < files.size(); ++i) {
        std::string file = files[i];
        if (use_bugged_files) {
            if (bugged_files.count(file) == 0) {
                continue;
            }
        }
        else {
            std::string file_path = P.getSrcdir() + "/" + file;
            // Turn off all .y .l generated file, a nasty hack here
            std::string base_file = replace_ext(file_path, ".y");
            if (existFile(base_file))
                continue;
            base_file = replace_ext(file_path, ".l");
            if (existFile(base_file))
                continue;
        }
        outlog_printf(1, "Processing %s\n", file.c_str());

        std::string code = M.getSourceCode(file);
        clang::ASTContext *ctxt = M.getSourceContext(file);

        std::map<SourcePositionTy, Stmt*> res =
            findCorrespondingStmt(P, ctxt, file, remaining_locs);

        {
            std::map<Stmt*, unsigned long> tmp;
            tmp.clear();
            std::map<SourcePositionTy, Stmt*>::iterator it;
            for (it = res.begin(); it != res.end(); it ++) {
                remaining_locs.erase(it->first);
                tmp.insert(std::make_pair(it->second, loc_rank_map[it->first]));
            }
            RepairCandidateGenerator G(M, file, tmp, naive, learning);
            G.setFlipP(GeoP);
            std::vector<RepairCandidate> res = G.run();
            for (size_t j = 0; j < res.size(); ++j ) {
                candidate_cnt += res[j].getCandidateAtoms().size();
                if (res[j].getCandidateAtoms().size() > 1) {
                    partial_candidate_cnt += res[j].getCandidateAtoms().size();
                }
                double final_score = computeScores(M, FP, EX, res[j], learning, random);
                q.push(std::make_pair(res[j], final_score));
            }
        }
    }

    size_t schema_cnt = q.size();
    outlog_printf(1, "Total %lu different repair schemas!!!!\n", schema_cnt);
    outlog_printf(1, "Total %lu different repair candidate templates for scoring!!!\n", candidate_cnt);
    outlog_printf(1, "Total %lu different partial repair candidate templates!!\n", partial_candidate_cnt);
    if (print_fix_only) {
        outlog_printf(1, "Print candidate templates...\n");
        FILE *fout = fopen(out_file.c_str(), "w");
        unsigned long cnt = 0;
        unsigned long blowup_cnt = 0;
        while (q.size() > 0) {
            RepairCandidateWithScore candidate_and_score = q.top();
            RepairCandidate candidate = candidate_and_score.first;
            q.pop();
            cnt ++;
            //llvm::errs() << cnt << "\n";
            //candidate.dump();
            fprintf(fout, "Rank %lu", cnt);
            if (PrintBlowupInfo.getValue()) {
                if (candidate.kind != RepairCandidate::AddInitKind &&
                        candidate.kind != RepairCandidate::AddAndReplaceKind &&
                        candidate.kind != RepairCandidate::ReplaceKind) {
                    std::set<Expr*> atoms = candidate.getCandidateAtoms();
                    blowup_cnt +=  atoms.size() * 2 - 1;
                }
                if (candidate.kind == RepairCandidate::TightenConditionKind ||
                        candidate.kind == RepairCandidate::LoosenConditionKind) {
                    IfStmt *stmt = llvm::dyn_cast<IfStmt>(candidate.actions[0].loc.stmt);
                    Expr* ori_cond = stmt->getCond();
                    clang::ASTContext *ctxt = M.getSourceContext(candidate.actions[0].loc.filename);
                    std::string expr_str = stmtToString(*ctxt, ori_cond);
                    unsigned long subexpr_cnt = 0;
                    size_t idx = 0;
                    while ((expr_str.find("&&", idx) != std::string::npos)
                            || (expr_str.find("||", idx) != std::string::npos)) {
                        size_t new_idx = expr_str.find("&&", idx);
                        size_t new_idx2 = expr_str.find("||", idx);
                        idx = new_idx + 1;
                        if (new_idx == std::string::npos)
                            idx = new_idx2 + 1;
                        if ((new_idx2 != std::string::npos) && (new_idx > new_idx2))
                            idx = new_idx2 + 1;
                        subexpr_cnt ++;
                    }
                    blowup_cnt += subexpr_cnt;
                }
                fprintf(fout, " BlowupCnt %lu\n", blowup_cnt);
            }
            else
                fprintf(fout, "\n");
            fprintf(fout, "%s", candidate.toString(M).c_str());
            if (learning) {
                fprintf(fout, "Score %.5lf\n", candidate_and_score.second);
                std::set<Expr*> atoms = candidate.getCandidateAtoms();
                if (atoms.size() > 1) {
                    fprintf(fout, "========Score Detail======\n");
                    for (std::set<Expr*>::iterator it = atoms.begin(); it != atoms.end(); ++it) {
                        clang::ASTContext *ctxt = M.getSourceContext(candidate.actions[0].loc.filename);
                        fprintf(fout, "%s %.5lf\n", stmtToString(*ctxt, *it).c_str(), candidate.scoreMap[*it]);
                        if (DumpFeatureDetail.getValue()) {
                            FeatureVector f = EX.extractFeature(M, candidate, *it);
                            dumpSignificantInVec(fout, FP, f, 0.1);
                        }
                    }
                }
                else if (DumpFeatureDetail.getValue()) {
                    FeatureVector f = EX.extractFeature(M, candidate, NULL);
                    dumpSignificantInVec(fout, FP, f, 0.1);
                }
            }
            else if (random) {
                fprintf(fout, "Score %.5lf\n", candidate_and_score.second);
            }
            fprintf(fout, "======================\n");
        }
        fclose(fout);
        return 0;
    }
    else {
        outlog_printf(1, "Trying different candidates!\n");
        ExprSynthesizer ES(P, M, q, naive, learning, FP);
        if (timeout_limit != 0)
            ES.setTimeoutLimit(timeout_limit);
        size_t cnt = 0;
        std::vector<std::pair<double, size_t> > resList;
        resList.clear();
        do {
            ExprSynthesizerResultTy res;
            bool ret = ES.workUntil(try_at_least, 0, res, full_synthesis, random);
            if (!ret) {
                if (cnt == 0)
                    outlog_printf(1, "Repair process ends without working fix!!\n");
                else
                    outlog_printf(1, "Repair process ends!");
                outlog_printf(1, "Total %lu different repair schemas!!!!\n", schema_cnt);
                outlog_printf(1, "Total %lu different repair candidate templates for scoring!!!\n", candidate_cnt);
                return 1;
            }
            else {
                std::string prefix_name = out_file;
                if ((out_file.size() >= 2) && (out_file.substr(out_file.size() - 2) == ".c"))
                    prefix_name = out_file.substr(0, out_file.size() - 2);
                for (ExprSynthesizerResultTy::iterator it2 = res.begin(); it2 != res.end();
                        ++it2) {
                    std::map<std::string, std::string> new_codes = it2->first;
                    for (std::map<std::string, std::string>::iterator it = new_codes.begin();
                            it != new_codes.end(); ++it) {
                        std::ostringstream sout;
                        // Here prefix_name is just a prefix
                        sout << prefix_name << replaceSlash(it->first);
                        if (cnt != 0)
                            sout << "-" << cnt;
                        outlog_printf(1, "Found a fix! Store to: %s\n", sout.str().c_str());
                        std::ofstream fout(sout.str().c_str(), std::ofstream::out);
                        fout << it->second;
                        fout.close();
                    }
                    resList.push_back(std::make_pair(-it2->second, cnt));
                    cnt ++;
                }
                // We are just going to rewrite the summary file
                if (summaryFile != "") {
                    sort(resList.begin(), resList.end());
                    std::ofstream fout(summaryFile.c_str(), std::ofstream::out);
                    for (size_t i = 0; i < resList.size(); i++)
                        fout << i << ": " << resList[i].second << " " << -resList[i].first << "\n";
                    fout.close();
                }
            }
            if (((timeout_limit > 0) && (get_timer() > timeout_limit))) {
                outlog_printf(1, "[%llu] Timeout! The limit is %llu!\n", get_timer(), timeout_limit);
                break;
            }
        }
        while (((try_at_least != 0) && (try_at_least > ES.getTestedCandidateNumber())));
        outlog_printf(1, "Repair process ends successfully!\n");
        outlog_printf(1, "Total %lu different repair schemas!!!!\n", schema_cnt);
        outlog_printf(1, "Total %lu different repair candidate templates for scoring!!!\n", candidate_cnt);
        outlog_printf(1, "Total %lu different partial repair candidate templates!!\n", partial_candidate_cnt);
        return 0;
    }
}
