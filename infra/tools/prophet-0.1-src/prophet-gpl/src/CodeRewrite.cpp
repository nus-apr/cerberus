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
#include "CodeRewrite.h"
#include "ExprSynthesizer.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ASTContext.h"
#include "llvm/Support/raw_ostream.h"
#include <string>

using namespace clang;

static std::string getNextToken(const std::string &str, size_t idx, size_t &next_idx) {
    size_t i = idx;
    while ((str[i] == '\n') || (str[i] == ' ') || (str[i] == '\t'))
        i++;
    std::string ret = "";
    while ((str[i] != '\n') && (str[i] != ' ') && (str[i] != '\t')) {
        ret.push_back(str[i]);
        i++;
    }
    next_idx = i;
    return ret;
}

bool canMerge(const CodeSegTy &codeSegs, const CodeSegTy &patches) {
    // So far we cannot merge the patch code that contains label
    // identifier, because we use nasty string manipulation.
    for (CodeSegTy::const_iterator it = patches.begin(); it != patches.end(); ++it) {
        assert(codeSegs.count(it->first) != 0);
        const std::vector<std::string> &tmp_vec = it->second;
        for (size_t i = 0; i < tmp_vec.size(); i++) {
            std::string patch = tmp_vec[i];
            size_t idx = 0;
            while (idx < patch.size()) {
                idx = patch.find(":", idx);
                if (idx != std::string::npos) {
                    if (idx + 1 <= patch.size())
                        if (patch[idx + 1] == ':') {
                            // Double "::", ignore
                            idx += 2;
                            continue;
                        }
                    size_t j = idx;
                    while (j > 0)
                        if (patch[j] != ';')
                            j --;
                        else
                            break;
                    size_t next_idx;
                    std::string token = getNextToken(patch, j, next_idx);
                    if (token != "case") {
                        bool multi_token = false;
                        for (size_t k = next_idx; k < idx; k++) {
                            if (patch[k] != '\n' && patch[k] != ' ' && patch[k] != '\t') {
                                multi_token = true;
                                break;
                            }
                        }
                        if (multi_token == false)
                            return false;
                    }
                    idx += 2;
                }
                else
                    break;
            }
            // We also cannot handle the case of declare statement
            // FIXME: this is just a heristic to get rid of this
            idx = 0;
            size_t idx3 = patch.find("{", 0);
            if (idx3 == std::string::npos) idx3 = patch.size();
            while (idx < patch.size() && (idx < idx3)) {
                idx = patch.find("\n", idx);
                if (idx == std::string::npos) break;
                size_t idx2 = idx + 1;
                while (idx2 < patch.size()) {
                    if ((patch[idx2] == ' ') || (patch[idx2] == '\t') || (patch[idx2] == '\n'))
                        idx2 ++;
                    else
                        break;
                }
                std::string token = "";
                while (idx2 < patch.size()) {
                    if ((patch[idx2] != ' ') && (patch[idx2] != '\t') && (patch[idx2] != '\n')) {
                        token.push_back(patch[idx2]);
                        idx2 ++;
                    }
                    else
                        break;
                }
                if (idx2 < idx3) {
                    if (token.size() > 0) {
                        if ((token == "unsigned") || (token == "int") || (token == "long") || (token == "char") ||
                            (token[token.size() - 1] == '*'))
                            return false;
                    }
                }
                idx = idx2;
            }
        }
    }
    return true;
}

bool getTrailingIndent(const std::string &str, std::string &indent_str) {
    size_t idx = str.size() - 1;
    while ((idx > 0) && (str[idx] == ' ' || str[idx] == '\t'))
        idx --;
    if (str[idx] != '\n')
        return false;
    else {
        indent_str = str.substr(idx+1);
        return true;
    }
}

std::string indentPatch(const std::string &patch, const std::string &indent_str) {
    std::vector<std::string> lines;
    lines.size();
    std::string tmp = "";
    for (size_t i = 0; i < patch.size(); i++) {
        tmp.push_back(patch[i]);
        if (patch[i] == '\n') {
            lines.push_back(tmp);
            tmp = "";
        }
    }
    if (tmp != "") lines.push_back(tmp);
    std::string ret = "";
    for (size_t i = 0; i < lines.size(); i++) {
        ret += lines[i];
        if (i != lines.size() - 1)
            ret += indent_str;
    }
    return ret;
}

NewCodeMapTy combineCode(const CodeSegTy &codeSegs, const CodeSegTy &patch) {
    assert( codeSegs.size() == patch.size() );
    NewCodeMapTy ret;
    ret.clear();
    for (CodeSegTy::const_iterator it = patch.begin(); it != patch.end(); ++it) {
        std::string src_file = it->first;
        CodeSegTy::const_iterator code_it = codeSegs.find(src_file);
        assert( code_it != codeSegs.end());
        const std::vector<std::string> &seg_vec = code_it->second;
        const std::vector<std::string> &patch_vec = it->second;
        assert( seg_vec.size() == patch_vec.size() + 1);
        ret[src_file] = "";
        ret[src_file] += seg_vec[0];
        std::string indent_str = "";
        for (size_t i = 0; i < patch_vec.size(); i++) {
            getTrailingIndent(seg_vec[i], indent_str);
            ret[src_file] += indentPatch(std::string("//prophet generated patch\n") +
                    patch_vec[i], indent_str) + seg_vec[i+1];
        }
    }
    return ret;
}

NewCodeMapTy mergeCode(const CodeSegTy &codeSegs, const std::vector<CodeSegTy> &patches) {
    CodeSegTy mergedPatch;
    mergedPatch.clear();
    for (CodeSegTy::const_iterator it = codeSegs.begin(); it != codeSegs.end(); ++it) {
        std::string src_file = it->first;
        mergedPatch[src_file].clear();
        CodeSegTy::const_iterator p_it = patches[0].find(src_file);
        assert( p_it != patches[0].end() );
        size_t n = p_it->second.size();
        assert( n == it->second.size() - 1);
        for (size_t j = 0; j < n; j ++) {
            std::string tmp_str = "";
            for (size_t i = 0; i < patches.size(); i++) {
                p_it = patches[i].find(src_file);
                assert( p_it != patches[i].end());
                assert(p_it->second.size() > j);
                std::ostringstream sout;
                if (i == 0)
                    sout << "if ";
                else
                    sout << "else if ";
                sout << "(__get_mutant()==" << i << ") {\n";
                sout << p_it->second[j];
                sout << "}\n";
                tmp_str += sout.str();
            }
            mergedPatch[src_file].push_back(tmp_str);
        }
    }
    return combineCode(codeSegs, mergedPatch);
}

static RepairCandidate replaceExprInCandidate(SourceContextManager &M,
        const RepairCandidate &rc, const ExprFillInfo &efi) {
    RepairCandidate ret = rc;
    ret.actions.clear();
    std::map<Stmt*, size_t> tmp_map1;
    std::map<Stmt*, std::map<Expr*, Expr*> > tmp_map2;
    tmp_map1.clear();
    tmp_map2.clear();
    for (size_t i = 0; i < rc.actions.size(); i++) {
        if (rc.actions[i].kind != RepairAction::ExprMutationKind) {
            tmp_map1[(Stmt*)rc.actions[i].ast_node] = ret.actions.size();
            ret.actions.push_back(rc.actions[i]);
        }
        else {
            Stmt *S = rc.actions[i].loc.stmt;
            if (tmp_map2.count(S) == 0)
                tmp_map2[S].clear();
            ExprFillInfo::const_iterator e_it = efi.find(i);
            assert( e_it != efi.end());
            tmp_map2[S].insert(std::make_pair((Expr*)rc.actions[i].ast_node,
                        e_it->second));
            if (tmp_map1.count(S) == 0) {
                tmp_map1[S] = ret.actions.size();
                // This is a old statement at all, we are going to add a replacemutation
                ret.actions.push_back(RepairAction(rc.actions[i].loc,
                            RepairAction::ReplaceMutationKind, S));
            }
        }
    }
    for (std::map<Stmt*, std::map<Expr*, Expr*> >::iterator it = tmp_map2.begin();
            it != tmp_map2.end(); ++it) {
        assert( tmp_map1.count(it->first) != 0);
        size_t idx = tmp_map1[it->first];
        ASTContext *ctxt = M.getSourceContext(ret.actions[idx].loc.filename);
        StmtReplacer R(ctxt, it->first);
        for (std::map<Expr*, Expr*>::iterator it2 = it->second.begin();
                it2 != it->second.end(); ++it2) {
            ParenExpr *E = new(*ctxt) ParenExpr(SourceLocation(), SourceLocation(), it2->second);
            R.addRule(it2->first, E);
        }
        ret.actions[tmp_map1[it->first]].ast_node = R.getResult();
    }
    return ret;
}

static std::pair<size_t, size_t> getStartEndOffset(SourceContextManager &M,
        const std::string &src_file, const ASTLocTy &loc) {
    ASTContext *Context = M.getSourceContext(loc.filename);
    SourceManager &manager = Context->getSourceManager();
    unsigned start_idx = manager.getFileOffset(manager.getExpansionLoc(loc.stmt->getLocStart()));
    unsigned end_idx = manager.getFileOffset(manager.getExpansionLoc(loc.stmt->getLocEnd()));
    std::string code = M.getSourceCode(loc.src_file);
    while (end_idx < code.size()) {
        if (code[end_idx] == '\n') {
            end_idx ++;
            break;
        }
        if (code[end_idx] == ';') {
            end_idx ++;
            if (end_idx < code.size() && code[end_idx] == '\n')
                end_idx ++;
            break;
        }
        end_idx ++;
    }
    return std::make_pair(start_idx, end_idx);
}

std::map<ASTLocTy, std::pair<std::string, bool> > eliminateAllNewLoc(SourceContextManager &M,
        const RepairCandidate &rc) {
    // We first construct the list of stmt close to each original ASTLocTy
    // and we store it to tmp_map1
    std::map<ASTLocTy, std::vector<Stmt*> > tmp_map1;
    std::map<Stmt*, ASTLocTy> tmp_map2;
    tmp_map1.clear();
    tmp_map2.clear();
    for (size_t i = 0; i < rc.actions.size(); i++) {
        // This is a new original statement
        if (tmp_map2.count(rc.actions[i].loc.stmt) == 0) {
            tmp_map2.insert(std::make_pair(rc.actions[i].loc.stmt, rc.actions[i].loc));
            tmp_map1[rc.actions[i].loc].clear();
            tmp_map1[rc.actions[i].loc].push_back(rc.actions[i].loc.stmt);
        }
        ASTLocTy rootLoc = tmp_map2[rc.actions[i].loc.stmt];
        Stmt* S = (Stmt*) rc.actions[i].ast_node;
        tmp_map2[S] = rootLoc;
        std::vector<Stmt*> &tmp_vec = tmp_map1[rootLoc];
        std::vector<Stmt*>::iterator pos = std::find(tmp_vec.begin(),
                tmp_vec.end(), rc.actions[i].loc.stmt);
        assert( pos != tmp_vec.end() );
        if (rc.actions[i].kind == RepairAction::ReplaceMutationKind)
            *pos = S;
        else if (rc.actions[i].kind == RepairAction::InsertMutationKind)
            tmp_vec.insert(pos, S);
        else {
            assert(rc.actions[i].kind == RepairAction::InsertAfterMutationKind);
            pos ++;
            if (pos == tmp_vec.end())
                tmp_vec.push_back(S);
            else
                tmp_vec.insert(pos, S);
        }
    }
    // We then get string from the list of stmt for each ASTLocTy
    std::map<ASTLocTy, std::pair<std::string, bool> > ret;
    ret.clear();
    for (std::map<ASTLocTy, std::vector<Stmt*> >::iterator it = tmp_map1.begin();
            it != tmp_map1.end(); ++it) {
        std::vector<Stmt*> &tmp_vec = it->second;
        ret[it->first].first = "";
        ret[it->first].second = !llvm::isa<CompoundStmt>(it->first.parent_stmt);
        for (size_t i = 0; i < tmp_vec.size(); i++) {
            ASTContext *ctxt = M.getSourceContext(it->first.filename);
            std::string tmp = stmtToString(*ctxt, tmp_vec[i]);
            ret[it->first].first += tmp;
            if (tmp[tmp.size() - 1]  != '\n' && tmp[tmp.size() - 1] != ';')
                ret[it->first].first += ";\n";
        }
    }
    return ret;
}

CodeRewriter::CodeRewriter(SourceContextManager &M, const RepairCandidate &rc, ExprFillInfo *pefi) {
    ExprFillInfo efi;
    if (pefi != NULL)
        efi = *pefi;
    else {
        efi.clear();
        // We are going to replace it with all unknown expressions
        for (size_t i = 0; i < rc.actions.size(); i++)
            if (rc.actions[i].kind == RepairAction::ExprMutationKind) {
                ASTContext *ctxt = M.getSourceContext(rc.actions[i].loc.filename);
                efi[i] = M.getUnknownExpr(ctxt, rc.actions[i].candidate_atoms);
            }
    }
    //rc.dump();
    // We first the rid of all ExprMutationKind in rc
    RepairCandidate rc1 = replaceExprInCandidate(M, rc, efi);
    //rc1.dump();
    // We then eliminate ASTLocTy with new statements, and replace them with
    // strings
    std::map<ASTLocTy, std::pair<std::string, bool> > res1 = eliminateAllNewLoc(M, rc1);
    // We then categorize location based on the src_file and their offset
    std::map<std::string, std::map<std::pair<size_t, size_t>, ASTLocTy> > res2;
    res2.clear();
    for (std::map<ASTLocTy, std::pair<std::string, bool> >::iterator it = res1.begin();
            it != res1.end(); ++it) {
        //llvm::errs() << "Location: " << it->first.toString(M) << "\n";
        //llvm::errs() << "patch: " << it->second.first << "\n";
        //llvm::errs() << "braket: " << it->second.second << "\n";
        ASTLocTy loc = it->first;
        std::string src_file = loc.src_file;
        if (res2.count(src_file) == 0)
            res2[src_file].clear();
        std::pair<size_t, size_t> offset_pair = getStartEndOffset(M, src_file, loc);
        //llvm::errs() << "offset: " << offset_pair.first << " " << offset_pair.second << "\n";
        // We reverse the start and end for sorting purpose
        res2[src_file].insert(std::make_pair(std::make_pair(offset_pair.second,
                        offset_pair.first), loc));
    }
    // Then we handle each source file saperately
    resCodeSegs.clear();
    resPatches.clear();
    for (std::map<std::string, std::map<std::pair<size_t, size_t>, ASTLocTy> >::iterator
            it = res2.begin(); it != res2.end(); ++it) {
        std::string src_file = it->first;
        resCodeSegs[src_file].clear();
        resPatches[src_file].clear();
        std::string code = M.getSourceCode(src_file);
        std::string cur_patch = "";
        long long cur_start = -1;
        long long cur_end = -1;
        long long last_end = 0;
        for (std::map<std::pair<size_t, size_t>, ASTLocTy>::iterator it2 = it->second.begin();
                it2 != it->second.end(); ++it2) {
            // NOTE: The start and the end are reversed
            long long start = it2->first.second;
            long long end = it2->first.first;
            assert( start >= last_end);
            if (cur_start == -1) {
                cur_start = start;
                cur_end = end;
                cur_patch = res1[it2->second].first;
                if (res1[it2->second].second)
                    cur_patch = std::string("{\n") + "    " + indentPatch(cur_patch, "    ") + "}\n";
            }
            else if (start<=cur_start && cur_end <= end) {
                // We need to merge these two, we first need to decide in the bigger one,
                // which part is not changed
                std::string top_part = code.substr(start, cur_start - start);
                std::string mid_part = code.substr(cur_start, cur_end);
                std::string bottom_part = code.substr(cur_end, end - cur_end);
                std::string big_patch = res1[it2->second].first;
                if (top_part + mid_part == big_patch.substr(0, cur_end - start)) {
                    cur_patch = top_part + cur_patch + big_patch.substr(cur_end - start);
                }
                else {
                    assert( mid_part + bottom_part ==
                            big_patch.substr(big_patch.size() - (end - cur_end)));
                    cur_patch = big_patch.substr(0, big_patch.size() - (end - cur_start))
                        + cur_patch + bottom_part;
                }
                if (res1[it2->second].second)
                    cur_patch = std::string("{\n") + "    " + indentPatch(cur_patch, "    ") + "}\n";
                cur_start = start;
                cur_end = end;
            }
            else {
                assert(start >= cur_end);
                resCodeSegs[src_file].push_back(code.substr(last_end, cur_start - last_end));
                resPatches[src_file].push_back(cur_patch);
                last_end = cur_end;
                cur_start = start;
                cur_end = end;
                cur_patch = res1[it2->second].first;
                if (res1[it2->second].second)
                    cur_patch = std::string("{\n") + "    " + indentPatch(cur_patch, "    ") + "}\n";
            }
        }
        if (cur_start != -1) {
            resCodeSegs[src_file].push_back(code.substr(last_end, cur_start - last_end));
            resPatches[src_file].push_back(cur_patch);
            resCodeSegs[src_file].push_back(code.substr(cur_end));
        }
    }
}
