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
#include "config.h"
#include "Utils.h"
#include "BenchProgram.h"
#include "RepairCandidateGenerator.h"
#include "ExprSynthesizer.h"
#include "ASTUtils.h"
#include "LocalAnalyzer.h"
#include "CodeRewrite.h"
#include "DuplicateDetector.h"
#include "FeatureParameter.h"
#include "llvm/Support/CommandLine.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/ASTContext.h"
#include <iostream>

using namespace clang;

#define CLANG_TEST_WRAP "tclang.py"
#define ISNEG_TMPFILE "/tmp/neg.tmp"
#define ISNEG_RECORDFILE "/tmp/neg.log"

#define BATCH_CAP 10
#define SYNC_CAP 200
#define SYNC_TIME_CAP 600

extern llvm::cl::opt<bool> ForCPP;

llvm::cl::opt<bool> CondExt("cond-ext", llvm::cl::init(false),
                            llvm::cl::desc("Enable condition extension"));
// XXX: OK, this is really shitty code for statistics
llvm::cl::opt<std::string> DumpPassedCandidate("dump-passed-candidate", llvm::cl::init(""),
        llvm::cl::desc("Dump the passed candidate, in order to collect experiments data!"));
size_t pass_global_cnt = 0;
size_t patch_explored = 0;

unsigned long tot_synthesis_run = 0;
unsigned long tot_concrete_conds = 0;
unsigned long tot_explored_templates = 0;

static unsigned long long the_timeout_limit = 0;

void dumpCandidate(SourceContextManager &M, const RepairCandidate &rc, Expr* v, double score) {
    std::ostringstream sout;
    sout << DumpPassedCandidate.getValue() << "-" << pass_global_cnt << ".txt";
    std::string fname = sout.str();
    std::ofstream fout(fname.c_str(), std::ofstream::out);
    fout << "Score: " << score << "\n";
    ASTContext *ctxt = M.getSourceContext(rc.actions[0].loc.filename);
    fout << "Var: " << stmtToString(*ctxt, v) << "\n";
    fout << rc.toString(M) << "\n";
    fout.close();
    pass_global_cnt ++;
}


static inline size_t locate_next(const std::string &s, size_t idx, int direction, std::string sub) {
    long long cur = idx;
    int cnt = 0;
    while (cur >= 0 && cur < (long long)s.size() && cnt >= 0) {
        cur = cur + direction;
        if (cur < 0) return std::string::npos;
        if (cur > (long long)s.size()) return std::string::npos;
        if (cnt == 0)
            if (s.substr(cur, sub.size()) == sub)
                return cur;
        if (s[cur] == '(')
            cnt += direction;
        if (s[cur] == ')')
            cnt -= direction;
    }
    return std::string::npos;
}

static inline size_t leftPos(size_t a, size_t b) {
    if (a != std::string::npos && ((a < b) || (b == std::string::npos)))
        return a;
    else
        return b;
}

static inline size_t rightPos(size_t a, size_t b) {
    if (a != std::string::npos && ((a > b) || (b == std::string::npos)))
        return a;
    else
        return b;
}

std::set<std::string> replaceIsNegWithClause(const std::string &code) {
    size_t idx = code.find("\n");
    idx = code.find(IS_NEG_HANDLER, idx);
    assert( idx != std::string::npos );

    size_t cnt = 1;
    size_t idx1 = idx + 9;
    while (cnt != 0) {
        if (code[idx1] == '(') cnt ++;
        if (code[idx1] == ')') cnt --;
        idx1 ++;
    }

    std::set<std::string> ret;
    ret.clear();

    // We always try 0 and 1
    ret.insert(code.substr(0, idx) + "(1)" + code.substr(idx1));
    ret.insert(code.substr(0, idx) + "(0)" + code.substr(idx1));

    // We are going to locate the left and right hand
    size_t left = locate_next(code, idx, -1, "(");
    left = locate_next(code, left, -1, "(");
    size_t right = locate_next(code, idx, 1, ")");
    right = locate_next(code, right, 1, ")");
    assert( left != std::string::npos);
    assert( right != std::string::npos);
    assert( right >= left);
    std::string s = code.substr(left, right - left + 1);
    //llvm::errs() << "The big clause: " << s << "\n";
    size_t cur_pos = 0;
    while ((s.find("&&", cur_pos) != std::string::npos) || (s.find("||", cur_pos) != std::string::npos)) {
        size_t pos1 = s.find("&&", cur_pos);
        size_t pos2 = s.find("||", cur_pos);
        if ((pos1 != std::string::npos) && ((pos1 < pos2) || (pos2 == std::string::npos)))
            cur_pos = pos1;
        else
            cur_pos = pos2;
        //llvm::errs() << s << " " << cur_pos << " " << s[cur_pos] << "\n";
        size_t sleft = locate_next(s, cur_pos, -1, "(");
        //llvm::errs() << sleft << " " << std::string::npos << "\n";
        sleft = rightPos(sleft, locate_next(s, cur_pos, -1, "&&"));
        sleft = rightPos(sleft, locate_next(s, cur_pos, -1, "||"));
        assert(sleft != std::string::npos);
        assert(sleft <= cur_pos);
        std::string subs;
        if (s[sleft] == '(')
            subs = s.substr(sleft + 1, cur_pos - sleft - 1);
        else
            subs = s.substr(sleft + 2, cur_pos - sleft - 2);
        std::string res = "";

        if (subs.find(IS_NEG_HANDLER) == std::string::npos) {
            //llvm::errs() << "Found a clause: " << subs << "\n";
            res = code.substr(0, idx) + "(" + subs + ")" + code.substr(idx1);
            //llvm::errs() << res.substr(idx - 200, idx1 - idx + 300) << "\n";
            ret.insert(res);
            res = code.substr(0, idx) + "(!" + "(" + subs + "))" + code.substr(idx1);
            //llvm::errs() << res.substr(idx - 200, idx1 - idx + 300) << "\n";
            ret.insert(res);
        }

        size_t sright = locate_next(s, cur_pos, 1, ")");
        sright = leftPos(sright, locate_next(s, cur_pos, 1, "&&"));
        sright = leftPos(sright, locate_next(s, cur_pos, 1, "||"));
        assert(sright != std::string::npos);
        assert(sright >= cur_pos);

        subs = s.substr(cur_pos + 2, sright - cur_pos - 2);

        if (subs.find(IS_NEG_HANDLER) == std::string::npos) {
            //llvm::errs() << "Found a clause: " << subs << "\n";
            res = code.substr(0, idx) + "(" + subs + ")" + code.substr(idx1);
            //llvm::errs() << res.substr(idx - 200, idx1 - idx + 300) << "\n";
            ret.insert(res);
            res = code.substr(0, idx) + "(!" + "(" + subs + "))" + code.substr(idx1);
            //llvm::errs() << res.substr(idx - 200, idx1 - idx + 300) << "\n";
            ret.insert(res);
        }
        cur_pos++;
    }
    return ret;
}

namespace {

double found_score = 0;

/*LocalAnalyzer* getLocalAnalyzer(SourceContextManager &M, const RepairCandidate &rc, size_t idx) {
    std::map<Stmt*, size_t> tmp_map;
    tmp_map.clear();
    for (size_t i = 0; i < idx; i++)
        if (rc.actions[i].kind != RepairAction::ExprMutationKind)
            tmp_map[(Stmt*)rc.actions[i].ast_node] = i;
    ASTLocTy cur_loc = rc.actions[idx].loc;
    // There is a corner case where the loc inserts the statement
    // as thee same as the location indication stmt
    Stmt* last_stmt = NULL;
    while (tmp_map.count(cur_loc.stmt) != 0) {
        cur_loc = rc.actions[tmp_map[cur_loc.stmt]].loc;
        if (cur_loc.stmt == last_stmt) break;
        last_stmt = cur_loc.stmt;
    }
    return M.getLocalAnalyzer(cur_loc);
}*/

Expr* createAbstractConditionExpr(SourceContextManager &M, const RepairAction &action) {
    ASTContext *ctxt = M.getSourceContext(action.loc.filename);
    std::vector<Expr*> tmp_argv;
    const ExprListTy &exprs = action.candidate_atoms;
    tmp_argv.clear();
    tmp_argv.push_back(getNewIntegerLiteral(ctxt, exprs.size()));
    for (size_t i = 0; i < exprs.size(); ++i) {
        ParenExpr *ParenE1 = new (*ctxt) ParenExpr(SourceLocation(), SourceLocation(), exprs[i]);
        UnaryOperator *AddrsOf = new (*ctxt)
            UnaryOperator(ParenE1, UO_AddrOf, ctxt->getPointerType(exprs[i]->getType()),
                    VK_RValue, OK_Ordinary, SourceLocation());
        tmp_argv.push_back(AddrsOf);
        ParenExpr *ParenE2 = new (*ctxt) ParenExpr(SourceLocation(), SourceLocation(), exprs[i]);
        UnaryExprOrTypeTraitExpr *SizeofE = new (*ctxt) UnaryExprOrTypeTraitExpr(
            UETT_SizeOf, ParenE2, ctxt->UnsignedLongTy, SourceLocation(), SourceLocation());
        tmp_argv.push_back(SizeofE);
    }
    Expr *abstract_cond = M.getInternalHandlerInfo(ctxt).abstract_cond;
    CallExpr *CE = new(*ctxt) CallExpr(*ctxt, abstract_cond, tmp_argv,
            ctxt->IntTy, VK_RValue, SourceLocation());
    return CE;
}

Expr* createAsciiStringLiteral(ASTContext *ctxt, const std::string &str_val) {
    StringLiteral *SL = StringLiteral::Create(*ctxt, str_val, StringLiteral::Ascii,
            false, ctxt->getConstantArrayType(ctxt->CharTy, llvm::APInt(32, str_val.size() + 1), ArrayType::Normal, 0),
            SourceLocation());
    ImplicitCastExpr *ICE1 = ImplicitCastExpr::Create(*ctxt, ctxt->getPointerType(ctxt->CharTy),
            CK_ArrayToPointerDecay, SL, 0, VK_RValue);
    ImplicitCastExpr *ICE2 = ImplicitCastExpr::Create(*ctxt, ctxt->getPointerType(ctxt->getConstType(ctxt->CharTy)),
            CK_BitCast, ICE1, 0, VK_RValue);
    return ICE2;
}

#define UNIQUE_TOKEN "##uni*##"

Expr* createUniqueStringToken(SourceContextManager &M, const RepairAction &action, Expr *oldRExpr) {
    ASTContext *ctxt = M.getSourceContext(action.loc.filename);
    StringLiteral *SL = llvm::dyn_cast<StringLiteral>(stripParenAndCast(oldRExpr));
    assert( SL );
    std::string string_val = SL->getString();
    // If it has %s or %n, we are not going to replace all of them
    size_t idx = string_val.rfind("%");
    if (idx == std::string::npos)
        string_val = UNIQUE_TOKEN;
    else {
        size_t j = idx + 1;
        while ((j < string_val.size() - 1) && ((string_val[j] > 'a') && (string_val[j] < 'z')))
            j++;
        string_val = string_val.substr(0, j) + UNIQUE_TOKEN;
    }
    return createAsciiStringLiteral(ctxt, string_val);
}

void enumerateExprImpl(SourceContextManager &M, const RepairCandidate &rc, long long mutate_idx, size_t i,
        std::set<ExprFillInfo> &ret, ExprFillInfo &cur_info) {
    if (i == rc.actions.size()) {
        ret.insert(cur_info);
        return;
    }
    if (rc.actions[i].kind != RepairAction::ExprMutationKind)
        enumerateExprImpl(M, rc, mutate_idx, i+1, ret, cur_info);
    else {
        //LocalAnalyzer *L = getLocalAnalyzer(M, rc, i);
        // If it is the condition synthesizer target, we are going to
        // create a special expr to replace it
        if (i == (size_t)mutate_idx) {
            if (rc.actions[i].tag == RepairAction::CondTag) {
                cur_info.insert(std::make_pair(i, createAbstractConditionExpr(M, rc.actions[i])));
                enumerateExprImpl(M, rc, mutate_idx, i + 1, ret, cur_info);
                cur_info.erase(i);
                return;
            }
            else {
                cur_info.insert(std::make_pair(i, createUniqueStringToken(M, rc.actions[i], rc.oldRExpr)));
                enumerateExprImpl(M, rc, mutate_idx, i + 1, ret, cur_info);
                cur_info.erase(i);
                return;
            }
        }
        else
            assert(0);
        /*
        Expr* E = (Expr*)rc.actions[i].ast_node;
        RepairAction::ExprTagTy tag = rc.actions[i].tag;
        if (tag == RepairAction::EnumTag) {
            // If it is an enum constant
            DeclRefExpr *DRE = llvm::dyn_cast<DeclRefExpr>(E);
            assert( DRE && (rc.actions[i].candidate_atoms.size() == 0));
            ValueDecl *VD = DRE->getDecl();
            // If this is a Enumerate, we are going to replace with other type
            if (llvm::isa<EnumConstantDecl>(VD)) {
                EnumConstantDecl *ECD = llvm::dyn_cast<EnumConstantDecl>(VD);
                ExprListTy exprs = L->getCandidateEnumConstant(ECD);
                for (size_t j = 0; j < exprs.size(); j++) {
                    cur_info.insert(std::make_pair(i, exprs[j]));
                    enumerateExprImpl(M, rc, cond_idx, i+1, ret, cur_info);
                    cur_info.erase(i);
                }
                return;
            }
        }
        else if (tag == RepairAction::ReturnTag || tag == RepairAction::ConstantTag) {
            assert( rc.actions[i].candidate_atoms.size() == 0);
            ExprListTy exprs;
            // If it is a return expr, newly created potentially
            if (tag == RepairAction::ReturnTag)
                exprs = L->getCandidateReturnExpr();
            else
                exprs = L->getCandidateConstantInType(E->getType());
            for (size_t j = 0; j < exprs.size(); ++j) {
                cur_info.insert(std::make_pair(i, exprs[j]));
                enumerateExprImpl(M, rc, cond_idx, i+1, ret, cur_info);
                cur_info.erase(i);
            }
            return;
        }
        else if (tag == RepairAction::VarTag || tag == RepairAction::CondTag) {
            // The normal variable replace
            for (size_t j = 0; j < rc.actions[i].candidate_atoms.size(); j++) {
                cur_info.insert(std::make_pair(i, rc.actions[i].candidate_atoms[j]));
                enumerateExprImpl(M, rc, cond_idx, i+1, ret, cur_info);
                cur_info.erase(i);
            }
        }
        */
    }
}

inline void out_codes(const CodeSegTy &a_code, const CodeSegTy &a_patch) {
    for (CodeSegTy::const_iterator it = a_code.begin(); it != a_code.end(); ++it) {
        outlog_printf(3, "//src_file:%s\n", it->first.c_str());
        CodeSegTy::const_iterator pit = a_patch.find(it->first);
        assert( pit != a_patch.end());
        const std::vector<std::string> &c_vec = it->second;
        const std::vector<std::string> &p_vec = pit->second;
        outlog_printf(3, "//Total frags: %lu\n", p_vec.size());
        outlog_printf(4, "//CodeSeg 0:\n%s\n", c_vec[0].c_str());
        for (size_t i = 0; i < p_vec.size(); i++) {
            outlog_printf(3, "//Patch %lu:\n%s\n", i, p_vec[i].c_str());
            outlog_printf(4, "//CodeSeg %lu:\n%s\n", i + 1, c_vec[i + 1].c_str());
        }
    }
}

std::set<ExprFillInfo> enumerateExprBindings(SourceContextManager &M,
        const RepairCandidate &rc, long long mutate_idx) {
    std::set<ExprFillInfo> ret;
    ExprFillInfo tmp;
    ret.clear();
    enumerateExprImpl(M, rc, mutate_idx, 0, ret, tmp);
    return ret;
}

double computeFinalScore(bool learning, SourceContextManager &M,
        const RepairCandidate &candidate, size_t id, Expr *E) {
    if (learning) {
        assert(candidate.actions.size() > 0);
        ASTContext *ast = M.getSourceContext(candidate.actions[0].loc.filename);
        Expr *E1 = NULL;
        if (E) {
            E1 = stripParenAndCast(E);
            if (isIntegerConstant(E1))
                E1 = NULL;
            if (E1) {
                BinaryOperator *BO = llvm::dyn_cast<BinaryOperator>(E1);
                if (BO)
                    E1 = BO->getLHS();
            }
        }
        for (std::map<Expr*, double>::const_iterator it = candidate.scoreMap.begin();
                it != candidate.scoreMap.end(); ++it)
            if (stmtToString(*ast, it->first) ==
                    stmtToString(*ast, E1))
                return it->second;
        assert(0);
    }
    else
        return candidate.score * 1000 - id;
}


typedef std::map<std::string, std::vector<std::string> > CodeSegTy;
typedef std::map<std::string, std::vector<std::string> > PatchListTy;
typedef std::map<std::string, std::string> NewCodeMapTy;

typedef BenchProgram::TestCaseSetTy TestCaseSetTy;

class BasicTester {
protected:
    BenchProgram &P;
    bool learning;
    SourceContextManager &M;
    TestCaseSetTy negative_cases, positive_cases;
    std::vector<RepairCandidate> candidates;
    std::vector<CodeSegTy> codes;
    std::vector<PatchListTy> patches;
    TestCaseSetTy failed_cases;
    bool naive;

    bool testOneCase(const BenchProgram::EnvMapTy &env, unsigned long t_id) {
        return P.test(std::string("src"), t_id, env, false);
    }

    bool testNegativeCases(const BenchProgram::EnvMapTy &env) {
        for (TestCaseSetTy::iterator it = negative_cases.begin();
                it != negative_cases.end(); it++)
            if (!testOneCase(env, *it))
                return false;
        outlog_printf(2, "Passed Negative Cases\n");
        return true;
    }

    bool testPositiveCases(const BenchProgram::EnvMapTy &env) {
        for (TestCaseSetTy::iterator it = failed_cases.begin();
                it != failed_cases.end(); it++) {
            if (!testOneCase(env, *it)) {
                outlog_printf(2, "Failed positive case %lu\n", *it);
                return false;
            }
        }
        for (TestCaseSetTy::iterator it = positive_cases.begin();
                it != positive_cases.end(); it++) {
            if (failed_cases.count(*it) != 0)
                continue;
            if (!testOneCase(env, *it)) {
                outlog_printf(2, "Failed positive case %lu\n", *it);
                failed_cases.insert(*it);
                return false;
            }
        }
        outlog_printf(2, "Passed Positive Cases\n");
        return true;
    }

    NewCodeMapTy cleanUpCode(const NewCodeMapTy &code) {
        NewCodeMapTy ret = code;
        for (NewCodeMapTy::iterator it = ret.begin(); it != ret.end(); ++it)
            it->second = M.cleanUpCode(it->second);
        return ret;
    }

    std::map<NewCodeMapTy, double> singleResult(const NewCodeMapTy &code, double score) {
        std::map<NewCodeMapTy, double> ret;
        ret.clear();
        ret.insert(std::make_pair(code, score));
        return ret;
    }

public:
    BasicTester(BenchProgram &P, bool learning, SourceContextManager &M, bool naive):
    P(P), learning(learning), M(M),
    negative_cases(P.getNegativeCaseSet()),
    positive_cases(P.getPositiveCaseSet()),
    candidates(),
    failed_cases(),
    naive(naive) {}

    virtual ~BasicTester() { }

    virtual bool canHandle(const RepairCandidate &candidate) {
        return true;
    }

    virtual CodeSegTy getCodeSegs(unsigned long id) {
        assert( id < codes.size() );
        return codes[id];
    }

    virtual CodeSegTy getPatches(unsigned long id) {
        assert( id < patches.size() );
        return patches[id];
    }

    virtual std::vector<unsigned long> preprocess(const RepairCandidate &candidate) {
        outlog_printf(2, "[%llu] Preprocess the following candidate with BasicTester:\n%s\n", get_timer(),
                candidate.toString(M).c_str());
        // We are going to create a set of binding ExprFillInfos
        std::set<ExprFillInfo> infos = enumerateExprBindings(M, candidate, -1);
        std::vector<unsigned long> res;
        res.clear();
        for (std::set<ExprFillInfo>::iterator it = infos.begin(); it != infos.end();
                ++it) {
            ExprFillInfo efi = *it;
            CodeRewriter R(M, candidate, &efi);
            CodeSegTy a_code = R.getCodeSegments();
            CodeSegTy a_patch = R.getPatches();
            {
                outlog_printf(2, "[%llu] BasicTester, a patch instance with id %lu:\n", get_timer(),
                        codes.size());
                out_codes(a_code, a_patch);
            }
            res.push_back((unsigned long)codes.size());
            candidates.push_back(candidate);
            codes.push_back(a_code);
            patches.push_back(a_patch);
            // OK, this is hacky, we are going to propagate this change to other place,
            // only here
            if (!naive) {
                DuplicateDetector D(M, a_code, a_patch);
                if (D.hasDuplicateCodeToPatch()) {
                    CodeSegTy a_new_code = D.getNewCodeSegments();
                    CodeSegTy a_new_patch = D.getNewPatches();
                    {
                        outlog_printf(2, "[%llu] BasicTester, a patch instance with id %lu (duplicate):\n", get_timer(),
                                codes.size());
                        out_codes(a_new_code, a_new_patch);
                    }
                    res.push_back(codes.size());
                    candidates.push_back(candidate);
                    codes.push_back(a_new_code);
                    patches.push_back(a_new_patch);
                }
            }
        }
        return res;
    }

    virtual clang::Expr* getFillExpr(size_t id) {
        return NULL;
    }

    virtual bool test(const BenchProgram::EnvMapTy &env, unsigned long id) {
        {
            outlog_printf(2, "[%llu] BasicTester, Testing instance id %lu:\n", get_timer(), id);
            out_codes(codes[id], patches[id]);
        }
        outlog_printf(3, "Testing negative cases!\n");
        if (!testNegativeCases(env)) {
            codes[id].clear();
            patches[id].clear();
            return false;
        }
        outlog_printf(3, "Testing positive cases!\n");
        bool ret = testPositiveCases(env);
        if (ret)
            outlog_printf(2, "[%llu] Passed!\n", get_timer());
        else {
            // We are going to clear out stuff tested, to avoid memory usage.
            codes[id].clear();
            patches[id].clear();
        }
        return ret;
    }

    virtual std::map<NewCodeMapTy, double> getResults(unsigned long id) {
        assert( candidates.size() > id);
        double score = computeFinalScore(learning, M, candidates[id], id, NULL);
        if (found_score < score) {
            found_score = score;
            outlog_printf(2, "Update best score %lf\n", found_score);
        }

        if (DumpPassedCandidate.getValue() != "")
            dumpCandidate(M, candidates[id], NULL, score);
        return singleResult(cleanUpCode(combineCode(codes[id], patches[id])), score);
    }
};

class StringConstTester : public BasicTester {
    std::map<unsigned long, std::set<std::string> > candidate_strs;
    std::vector<ExprFillInfo> infos;

    bool parseFile(std::vector<std::string> &res, const std::string &fname) {
        res.clear();
        std::ifstream fin(fname.c_str(), std::ifstream::in);
        if (!fin.is_open())
            return false;
        std::string line;
        while (fin) {
            getline(fin, line);
            res.push_back(line);
        }
        return true;
    }

    bool compareStr(const std::vector<std::string> &out_lines,
            const std::vector<std::string> &exp_lines, std::string &replace_str) {
        replace_str = "";
        // FIXME: I hate this code, but I cannot find a better way to do it
        if (out_lines.size() != exp_lines.size())
            return false;
        for (size_t i = 0; i < out_lines.size(); i++) {
            unsigned long token_idx = out_lines[i].find(UNIQUE_TOKEN);
            if (token_idx != std::string::npos) {
                // We first going to identify the longest substr in exp as the
                // match up point. It can be done with O(N+M) with extended KMP
                // but I am lazy. Just a line, bah
                size_t maximum_cnt = 0;
                size_t match_idx = 0;
                if (token_idx > 0) {
                    for (size_t j = 0; j < exp_lines[i].size(); j++) {
                        size_t i1 = token_idx - 1;
                        size_t j1 = j;
                        size_t cnt = 0;
                        while ((i1 > 0) && (j1 > 0)) {
                            if (out_lines[i][i1] == exp_lines[i][j1]) {
                                i1 --;
                                j1 --;
                                cnt ++;
                            }
                            else
                                break;
                        }
                        if (out_lines[i][i1] == exp_lines[i][j1])
                            cnt ++;
                        if (cnt > maximum_cnt) {
                            maximum_cnt = cnt;
                            match_idx = j + 1;
                        }
                    }
                    // This is weird, not likely to be correct.
                    if (maximum_cnt == 0)
                        return false;
                }

                // Now we are going to find identify the longest substr in
                // exp that can match substr starts from token_idx + UNIQUE_TOKEN in out
                maximum_cnt = 0;
                size_t match2_idx = 0;
                for (size_t j = match_idx; j <= exp_lines[i].size(); j++) {
                    size_t i1 = token_idx + std::string(UNIQUE_TOKEN).size();
                    size_t j1 = j;
                    size_t cnt = 0;
                    while ((i1 < out_lines[i].size()) && (j1 < exp_lines[i].size())) {
                        if (out_lines[i][i1] == exp_lines[i][j1]) {
                            i1 ++;
                            j1 ++;
                            cnt ++;
                        }
                        else
                            break;
                    }
                    if (i1 == out_lines[i].size() && j1 == exp_lines[i].size())
                        cnt ++;
                    if (cnt > maximum_cnt) {
                        maximum_cnt = cnt;
                        match2_idx = j;
                    }
                }
                // Now the replace_str should equal to stuff between
                // match_idx and match2_idx
                std::string new_replace = exp_lines[i].substr(match_idx, match2_idx - match_idx);
                if ((replace_str != "") && (new_replace != replace_str))
                    return false;
                replace_str = new_replace;
            }
        }
        return true;
        /*// This does not work because of %s and %d in stupid php exp files
        unsigned long cnt = 0;
        unsigned long i = 0;
        while ((i = out_str.find(UNIQUE_TOKEN, i)) != std::string::npos) {
            cnt ++;
            i ++;
        }
        unsigned long token_size = std::string(UNIQUE_TOKEN).size();
        unsigned long fixed_size = out_str.size() - token_size * cnt;
        unsigned long missing = exp_str.size() - fixed_size;
        if (missing % cnt != 0)
            return false;
        unsigned long each_len = missing / cnt;
        replace_str = "";
        unsigned long j = 0;
        for (size_t i = 0; i < out_str.size(); i++) {
            if (out_str.substr(i, token_size) == UNIQUE_TOKEN) {
                std::string tmp = exp_str.substr(j, each_len);
                if ((replace_str == tmp) || (replace_str == ""))
                    replace_str = tmp;
                else
                    return false;
                i += token_size - 1;
                j += each_len;
            }
            else if (out_str[i] != exp_str[j])
                return false;
            else
                j ++;
        }
        return true;*/
    }

    Expr* createNewStringExpr(ASTContext *ctxt, Expr *oldExpr, const std::string &replace_str) {
        StringLiteral *SL = llvm::dyn_cast<StringLiteral>(stripParenAndCast(oldExpr));
        assert (SL);
        std::string old_str = SL->getString();
        unsigned long idx = old_str.find(UNIQUE_TOKEN);
        assert( idx != std::string::npos);
        std::string new_str = old_str.substr(0, idx) + replace_str + old_str.substr(idx + std::string(UNIQUE_TOKEN).size());
        return createAsciiStringLiteral(ctxt, new_str);
    }

public:
    StringConstTester(BenchProgram &P, bool learning, SourceContextManager &M, bool naive):
        BasicTester(P, learning, M, naive), candidate_strs(), infos() { }

    virtual ~StringConstTester() { }

    int getMutateId(const RepairCandidate &rc) {
        for (int i = 0; i < (int)rc.actions.size(); ++i)
            if (rc.actions[i].kind == RepairAction::ExprMutationKind)
                if (rc.actions[i].tag == RepairAction::StringConstantTag)
                    return i;
        return -1;
    }

    virtual bool canHandle(const RepairCandidate &candidate) {
        return getMutateId(candidate) != -1;
    }

    virtual CodeSegTy getCodeSegs(unsigned long id) {
        assert( id < codes.size() );
        return codes[id];
    }

    virtual CodeSegTy getPatches(unsigned long id) {
        assert( id < patches.size() );
        return patches[id];
    }

    virtual std::vector<unsigned long> preprocess(const RepairCandidate &candidate) {
        outlog_printf(2, "[%llu] Preprocess the following candidate with StringConstTester:\n%s\n", get_timer(),
                candidate.toString(M).c_str());
        // We are going to create a set of binding ExprFillInfos
        std::set<ExprFillInfo> the_infos = enumerateExprBindings(M, candidate, getMutateId(candidate));
        std::vector<unsigned long> res;
        res.clear();
        for (std::set<ExprFillInfo>::iterator it = the_infos.begin(); it != the_infos.end();
                ++it) {
            ExprFillInfo efi = *it;
            CodeRewriter R(M, candidate, &efi);
            CodeSegTy a_code = R.getCodeSegments();
            CodeSegTy a_patch = R.getPatches();
            {
                outlog_printf(2, "[%llu] StringConstTester, a patch instance with id %lu:\n", get_timer(),
                        codes.size());
                out_codes(a_code, a_patch);
            }
            res.push_back((unsigned long)codes.size());
            candidates.push_back(candidate);
            codes.push_back(a_code);
            patches.push_back(a_patch);
            infos.push_back(*it);
            // OK, this is hacky, we are going to propagate this change to other place,
            // only here
            if (!naive) {
                DuplicateDetector D(M, a_code, a_patch);
                if (D.hasDuplicateCodeToPatch()) {
                    CodeSegTy a_new_code = D.getNewCodeSegments();
                    CodeSegTy a_new_patch = D.getNewPatches();
                    {
                        outlog_printf(2, "[%llu] StringConstTester, a patch instance with id %lu (duplicate):\n", get_timer(),
                                codes.size());
                        out_codes(a_new_code, a_new_patch);
                    }
                    res.push_back(codes.size());
                    candidates.push_back(candidate);
                    codes.push_back(a_new_code);
                    patches.push_back(a_new_patch);
                    infos.push_back(*it);
                }
            }
        }
        return res;
    }

    virtual clang::Expr* getFillExpr(size_t id) {
        return NULL;
    }

    virtual bool test(const BenchProgram::EnvMapTy &env, unsigned long id) {
        {
            outlog_printf(2, "[%llu] StringConstTester, Testing instance id %lu:\n", get_timer(), id);
            out_codes(codes[id], patches[id]);
        }
        outlog_printf(3, "Testing negative cases!\n");
        candidate_strs[id].clear();
        for (TestCaseSetTy::iterator it = negative_cases.begin();
                it != negative_cases.end(); it++) {
            std::string tmp_out = "/tmp/__out.str";
            std::string tmp_exp = "/tmp/__exp.str";
            BenchProgram::EnvMapTy new_env = env;
            new_env["OUTIFFAIL"] = tmp_out;
            new_env["EXPIFFAIL"] = tmp_exp;
            {
                std::string cmd = "rm -rf " + tmp_out;
                int ret = system(cmd.c_str());
                assert( ret == 0);
                cmd = "rm -rf " + tmp_exp;
                ret = system(cmd.c_str());
                assert( ret == 0);
            }
            if (!testOneCase(new_env, *it)) {
                bool may_pass = false;
                std::vector<std::string> outstr, expstr;
                if (parseFile(outstr, tmp_out))
                    if (parseFile(expstr, tmp_exp)) {
                        std::string replace_str;
                        if (compareStr(outstr, expstr, replace_str)) {
                            // If it may pass with some substitution
                            candidate_strs[id].insert(replace_str);
                            may_pass = true;
                        }
                    }
                if (!may_pass || candidate_strs[id].size() > 1) {
                    codes[id].clear();
                    candidate_strs[id].clear();
                    patches[id].clear();
                    {
                        std::string cmd = "rm -rf " + tmp_out;
                        int ret = system(cmd.c_str());
                        assert( ret == 0);
                        cmd = "rm -rf " + tmp_exp;
                        ret = system(cmd.c_str());
                        assert( ret == 0);
                    }
                    return false;
                }
            }
            else {
                // XXX: OK, althogh it makes it passes, it got to be an incorrect patch, we just skip it
                return false;
            }
            {
                std::string cmd = "rm -rf " + tmp_out;
                int ret = system(cmd.c_str());
                assert( ret == 0);
                cmd = "rm -rf " + tmp_exp;
                ret = system(cmd.c_str());
                assert( ret == 0);
            }
        }


        // We just skip test positive right now, we are going to check them
        // at postprocess anyway
        /*outlog_printf(3, "Testing positive cases!\n");
        bool ret = testPositiveCases(env);
        if (ret)
            outlog_printf(2, "Passed!\n");
        else {
            // We are going to clear out stuff tested, to avoid memory usage.
            codes[id].clear();
            patches[id].clear();
            candidate_strs[id].clear();
            assert(0);
        }
        return ret;*/
        outlog_printf(2, "[%llu] May pass, will check when postprocessing, with:\n%s\n", get_timer(), candidate_strs[id].begin()->c_str());
        return true;
    }

    virtual std::map<NewCodeMapTy, double> getResults(unsigned long id) {
        outlog_printf(2, "[%llu] StringConstTester postprocessing! \n", get_timer());
        RepairCandidate candidate = candidates[id];
        unsigned long mutate_id = getMutateId(candidate);
        assert( candidate_strs[id].size() == 1);
        ExprFillInfo efi = infos[id];
        ASTContext *ctxt = M.getSourceContext(candidate.actions[mutate_id].loc.filename);
        efi[mutate_id] = createNewStringExpr(ctxt, efi[mutate_id], *candidate_strs[id].begin());

        CodeRewriter R(M, candidate, &efi);
        NewCodeMapTy code = R.getCodes();
        BenchProgram::EnvMapTy buildEnv;
        buildEnv.clear();
        if (ForCPP.getValue())
            buildEnv["COMPILE_CMD"] = "clang++";
        else
            buildEnv["COMPILE_CMD"] = GCC_CMD;
        bool build_succ = P.buildWithRepairedCode(CLANG_TEST_WRAP, buildEnv, code);
        if (!build_succ) {
            outlog_printf(2, "Build failed!");
            return std::map<NewCodeMapTy, double>();
        }

        bool passed = testNegativeCases(BenchProgram::EnvMapTy());
        if (!passed) {
            outlog_printf(2, "Failed negative cases!");
            return std::map<NewCodeMapTy, double>();
        }
        passed = testPositiveCases(BenchProgram::EnvMapTy());
        if (!passed) {
            outlog_printf(2, "Failed positive cases!");
            return std::map<NewCodeMapTy, double>();
        }

        double score = computeFinalScore(learning, M, candidates[id], id, NULL);
        if (found_score < score) {
            found_score = score;
            outlog_printf(2, "[%llu] Update best score %lf\n", get_timer(), found_score);
        }

        if (DumpPassedCandidate.getValue() != "")
            dumpCandidate(M, candidate, NULL, score);

        return singleResult(cleanUpCode(code), score);
    }
};

#define MAGIC_NUMBER -123456789

long checkV(const std::map<unsigned long, std::vector< std::vector< long long> > > &caseVMap,
    const std::set<unsigned long> &negative_cases, const std::set<unsigned long> &positive_cases,
    const std::map<unsigned long, std::vector<unsigned long> > &negative_records,
    size_t idx, long long v, int flag) {

    long ret = 0;

    for (std::set<unsigned long>::iterator it = positive_cases.begin();
            it != positive_cases.end(); ++it) {
        std::map<unsigned long, std::vector< std::vector< long long> > >::const_iterator cit;
        cit = caseVMap.find(*it);
        assert( cit != caseVMap.end());
        for (size_t i = 0; i < cit->second.size(); i++) {
            assert(cit->second[i][idx] != MAGIC_NUMBER && "sanity check!");
            int flag_mask = flag & 3;
            int flag_bit = flag & 4;
            long long rv = v;
            if (flag_bit != 0)
                rv = cit->second[i][v];
            bool cond;
            switch (flag_mask) {
                case 0:
                    cond = (cit->second[i][idx] != rv);
                    break;
                case 1:
                    cond = (cit->second[i][idx] == rv);
                    break;
                case 2:
                    cond = (cit->second[i][idx] < rv);
                    break;
                case 3:
                    cond = (cit->second[i][idx] > rv);
                    break;
                default:
                    break;
            }
            if (cond) {
                ret += 2;
                break;
            }
        }
    }

    bool valid = false;
    for (std::set<unsigned long>::iterator it = negative_cases.begin();
            it != negative_cases.end(); ++it) {
        std::map<unsigned long, std::vector< std::vector< long long> > >::const_iterator cit;
        cit = caseVMap.find(*it);
        assert( cit != caseVMap.end());
        std::map<unsigned long, std::vector<unsigned long> >::const_iterator nit;
        nit = negative_records.find(*it);
        if (cit->second.size() != nit->second.size()) {
            outlog_printf(1, "Seems some non-determinism! %lu v.s. %lu Length mismatch!\n",
                    (unsigned long)cit->second.size(), (unsigned long)nit->second.size());
            return -1;
        }
        for (size_t i = 0; i < cit->second.size(); i++) {
            assert(cit->second[i][idx] != MAGIC_NUMBER && "sanity check!");

            int flag_mask = flag & 3;
            int flag_bit = flag & 4;
            long long rv = v;
            if (flag_bit != 0) {
                rv = cit->second[i][v];
            }
            bool cond;
            switch (flag_mask) {
                case 0:
                    cond = (cit->second[i][idx] != rv);
                    break;
                case 1:
                    cond = (cit->second[i][idx] == rv);
                    break;
                case 2:
                    cond = (cit->second[i][idx] < rv);
                    break;
                case 3:
                    cond = (cit->second[i][idx] > rv);
                    break;
                default:
                    break;
            }

            if (cond)
                valid = true;
            if ((nit->second[i] == 0) && (cond)) {
                ret++;
                break;
            }
            if ((nit->second[i] == 1) && (!cond)) {
                ret++;
                break;
            }
        }
    }
    if (valid)
        return ret;
    else
        return -1;
}

struct SynResTy {
    size_t idx;
    long long v;
    size_t flag;
    SynResTy(): idx(), v(), flag() {}

    SynResTy(size_t idx, long long v, size_t flag):
        idx(idx), v(v), flag(flag) {}

    bool operator < (const SynResTy &a) const {
        if (flag != a.flag)
            return flag > a.flag;
        else if (idx != a.idx)
            return idx < a.idx;
        else
            return v < a.v;
    }
};

static int compareTypeCheck(Expr* E1, Expr* E2) {
    QualType T1 = E1->getType();
    QualType T2 = E2->getType();
    if (T1->isIntegerType() == T2->isIntegerType())
        return 0;
    if (T1->isPointerType() == T2->isPointerType())
        return 1;
    return -1;
}

std::vector<Expr*> synthesizeResult(ExprListTy exprs,
        const std::map<unsigned long, std::vector<unsigned long> > &negative_records,
        const std::map<unsigned long, std::vector< std::vector< long long> > > &caseVMap,
        const std::set<unsigned long> &negative_cases,
        const std::set<unsigned long> &positive_cases, ASTContext *ctxt) {
    std::vector<std::pair<size_t, SynResTy> > res;
    res.clear();
    // If just remove work, then we remove it
    /*bool no_pos_exec = true;
    for (std::set<unsigned long>::const_iterator it = positive_cases.begin();
            it != positive_cases.end(); ++it) {
        std::map<unsigned long, std::vector< std::vector<long long> > > ::const_iterator find_it;
        find_it = caseVMap.find(*it);
        if (find_it->second.size() != 0) {
            no_pos_exec = false;
            break;
        }
    }
    if (no_pos_exec)
        res.push_back(std::make_pair(0, SynResTy(0, 1, 2)));*/
    // Collect over all possible values for a variable
    for (size_t vid = 0; vid < exprs.size(); vid++) {
        std::set<long long> vals;
        vals.clear();
        bool give_up = false;
        for (std::map<unsigned long, std::vector< std::vector< long long> > >::const_iterator
                it = caseVMap.begin(); it != caseVMap.end(); ++it) {
            for (size_t i = 0; i < it->second.size(); i++) {
                if (it->second[i][vid] == MAGIC_NUMBER)
                    give_up = true;
                // This is to avoid catch those pointer values, they are not useful at all
                if ((it->second[i][vid] < 1000) && (it->second[i][vid] > -1000))
                    vals.insert(it->second[i][vid]);
            }
        }
        if (give_up) continue;
        for (std::set<long long>::iterator it = vals.begin(); it != vals.end(); it++) {
            size_t flag_e = 2;
            if (CondExt.getValue())
                if (exprs[vid]->getType()->isIntegerType())
                    flag_e = 4;
            for (size_t flag_v = 0; flag_v < flag_e; flag_v ++) {
                long long the_v = *it;
                if (flag_v == 2)
                    the_v ++;
                else if (flag_v == 3)
                    the_v --;
                long vio = checkV(caseVMap, negative_cases, positive_cases,
                        negative_records, vid, the_v, flag_v);
                if (vio >= 0)
                    res.push_back(std::make_pair((size_t)vio, SynResTy(vid, the_v, flag_v)));
            }
        }
        if (CondExt.getValue()) {
            for (size_t vid2 = 0; vid2 < exprs.size(); vid2 ++) {
                int checkType = compareTypeCheck(exprs[vid], exprs[vid2]);
                if (checkType == -1)
                    continue;
                bool give_up = false;
                for (std::map<unsigned long, std::vector< std::vector< long long> > >::const_iterator
                    it = caseVMap.begin(); it != caseVMap.end(); ++it) {
                    for (size_t i = 0; i < it->second.size(); i++) {
                        if (it->second[i][vid2] == MAGIC_NUMBER) {
                            give_up = true;
                            break;
                        }
                    }
                    if (give_up) break;
                }
                if (give_up)
                    continue;
                size_t flag_e = 8;
                if (checkType == 1)
                    flag_e = 6;
                for (size_t flag_v = 4; flag_v < flag_e; flag_v ++) {
                    long vio = checkV(caseVMap, negative_cases, positive_cases,
                            negative_records, vid, vid2, flag_v);
                    if (vio >= 0)
                        res.push_back(std::make_pair((size_t)vio, SynResTy(vid, vid2, flag_v)));
                }
            }
        }
    }

    tot_synthesis_run ++;
    tot_concrete_conds += res.size() + 1;

    std::sort(res.begin(), res.end());
    std::vector<Expr*> ret;
    ret.clear();
    ret.push_back(getNewIntegerLiteral(ctxt, 1));
    for (size_t i = 0; i < res.size(); i++)
        if (i < 20 || res[i].first == 0)
        {
            SynResTy &tmp = res[i].second;
            Expr *E;
            Expr *RHS;
            int flag_mask = (tmp.flag & 3);
            int flag_bit = (tmp.flag & 4);
            if (flag_bit == 0)
                RHS = getNewIntegerLiteral(ctxt, tmp.v);
            else
                RHS = exprs[tmp.v];
            BinaryOperatorKind bkind;
            switch (flag_mask) {
                case 0:
                    bkind = BO_NE;
                    break;
                case 1:
                    bkind = BO_EQ;
                    break;
                case 2:
                    bkind = BO_LE;
                    break;
                case 3:
                    bkind = BO_GT;
                    break;
                default:
                    assert(0);
            }
            E = new(*ctxt) BinaryOperator(
                exprs[tmp.idx], RHS, bkind, ctxt->IntTy, VK_RValue,
                OK_Ordinary, SourceLocation(), false);
            if (bkind == BO_EQ)
                ret.push_back(getParenExpr(ctxt, E));
            else
                ret.push_back(E);
        }
        else
            break;

    return ret;
}

std::vector<Expr*> synthesizeResultSPR(ExprListTy exprs,
        const std::map<unsigned long, std::vector<unsigned long> > &negative_records,
        const std::map<unsigned long, std::vector< std::vector< long long> > > &caseVMap,
        const std::set<unsigned long> &negative_cases,
        const std::set<unsigned long> &positive_cases, ASTContext *ctxt) {
    std::vector<std::pair<size_t, SynResTy> > res;
    res.clear();
    // Collect over all possible values for a variable
    for (size_t vid = 0; vid < exprs.size(); vid++) {
        std::set<long long> vals;
        vals.clear();
        bool give_up = false;
        for (std::map<unsigned long, std::vector< std::vector< long long> > >::const_iterator
                it = caseVMap.begin(); it != caseVMap.end(); ++it) {
            for (size_t i = 0; i < it->second.size(); i++) {
                if (it->second[i][vid] == MAGIC_NUMBER)
                    give_up = true;
                // This is to avoid catch those pointer values, they are not useful at all
                if ((it->second[i][vid] < 1000) && (it->second[i][vid] > -1000))
                    vals.insert(it->second[i][vid]);
            }
        }
        if (give_up) continue;
        for (std::set<long long>::iterator it = vals.begin(); it != vals.end(); it++) {
            size_t flag_e = 2;
            if (CondExt.getValue())
                if (exprs[vid]->getType()->isIntegerType())
                    flag_e = 4;
            for (size_t flag_v = 0; flag_v < flag_e; flag_v ++) {
                long long the_v = *it;
                if (flag_v == 2)
                    the_v ++;
                else if (flag_v == 3)
                    the_v --;
                long vio = checkV(caseVMap, negative_cases, positive_cases,
                        negative_records, vid, the_v, flag_v);
                if (vio >= 0)
                    res.push_back(std::make_pair((size_t)vio, SynResTy(vid, the_v, flag_v)));
            }
        }
        if (CondExt.getValue()) {
            for (size_t vid2 = 0; vid2 < exprs.size(); vid2 ++) {
                int checkType = compareTypeCheck(exprs[vid], exprs[vid2]);
                if (checkType == -1)
                    continue;
                bool give_up = false;
                for (std::map<unsigned long, std::vector< std::vector< long long> > >::const_iterator
                    it = caseVMap.begin(); it != caseVMap.end(); ++it) {
                    for (size_t i = 0; i < it->second.size(); i++) {
                        if (it->second[i][vid2] == MAGIC_NUMBER) {
                            give_up = true;
                            break;
                        }
                    }
                    if (give_up) break;
                }
                if (give_up)
                    continue;
                size_t flag_e = 8;
                if (checkType == 1)
                    flag_e = 6;
                for (size_t flag_v = 4; flag_v < flag_e; flag_v ++) {
                    long vio = checkV(caseVMap, negative_cases, positive_cases,
                            negative_records, vid, vid2, flag_v);
                    if (vio >= 0)
                        res.push_back(std::make_pair((size_t)vio, SynResTy(vid, vid2, flag_v)));
                }
            }
        }
    }

    tot_synthesis_run ++;
    tot_concrete_conds += res.size() + 1;

    std::sort(res.begin(), res.end());
    std::vector<Expr*> ret;
    ret.clear();
    ret.push_back(getNewIntegerLiteral(ctxt, 1));
    for (size_t i = 0; i < res.size(); i++)
        if (i < 20 || res[i].first == 0)
        {
            SynResTy &tmp = res[i].second;
            Expr *E;
            if (tmp.v == 0 && (tmp.flag == 0 || tmp.flag == 1)) {
                Expr *RHS;
                int flag_mask = tmp.flag & 3;
                int flag_bit = tmp.flag & 4;
                if (flag_bit == 0)
                    RHS = getNewIntegerLiteral(ctxt, tmp.v);
                else
                    RHS = exprs[tmp.v];
                BinaryOperatorKind bkind;
                switch (flag_mask) {
                    case 0:
                        bkind = BO_NE;
                        break;
                    case 1:
                        bkind = BO_EQ;
                        break;
                    case 2:
                        bkind = BO_LE;
                        break;
                    case 3:
                        bkind = BO_GT;
                        break;
                    default:
                        assert(0);
                }
                E = new(*ctxt) BinaryOperator(
                    exprs[tmp.idx], RHS, bkind, ctxt->IntTy, VK_RValue,
                    OK_Ordinary, SourceLocation(), false);
                ret.push_back(E);
            }
        }
        else
            break;
    for (size_t i = 0; i < res.size(); i++)
        if (i < 20 || res[i].first == 0)
        {
            SynResTy &tmp = res[i].second;
            Expr *E;
            if (tmp.v != 0 || (tmp.flag != 0 && tmp.flag != 1)) {
                Expr *RHS;
                int flag_mask = tmp.flag & 3;
                int flag_bit = tmp.flag & 4;
                if (flag_bit == 0)
                    RHS = getNewIntegerLiteral(ctxt, tmp.v);
                else
                    RHS = exprs[tmp.v];
                BinaryOperatorKind bkind;
                switch (flag_mask) {
                    case 0:
                        bkind = BO_NE;
                        break;
                    case 1:
                        bkind = BO_EQ;
                        break;
                    case 2:
                        bkind = BO_LE;
                        break;
                    case 3:
                        bkind = BO_GT;
                        break;
                    default:
                        assert(0);
                }
                E = new(*ctxt) BinaryOperator(
                    exprs[tmp.idx], RHS, bkind, ctxt->IntTy, VK_RValue,
                    OK_Ordinary, SourceLocation(), false);
                ret.push_back(E);
            }
        }
        else
            break;

    return ret;
}


bool isZeroConstantExpr(Expr *E) {
    BinaryOperator *BO = llvm::dyn_cast<BinaryOperator>(E);
    if (!BO) return false;
    IntegerLiteral *IL = llvm::dyn_cast<IntegerLiteral>(BO->getRHS());
    if (!IL) return false;
    return (IL->getValue() == 0);
}

class ConstantCondVisitor : public RecursiveASTVisitor<ConstantCondVisitor> {
    std::set<std::string> res;
    ASTContext *ast;

    void addTo(Expr *E) {
        Expr *E1 = stripParenAndCast(E);
        if (llvm::isa<DeclRefExpr>(E1) || llvm::isa<MemberExpr>(E1))
            res.insert(stmtToString(*ast, E1));
    }

public:
    ConstantCondVisitor(ASTContext *ast): res(), ast(ast) {
        res.clear();
    }

    virtual bool VisitParenExpr(ParenExpr *PE) {
        addTo(PE->getSubExpr());
        return true;
    }

    virtual bool VisitBinLT(BinaryOperator *BO) {
        addTo(BO->getLHS());
        addTo(BO->getRHS());
        return true;
    }

    virtual bool VisitBinGT(BinaryOperator *BO) {
        addTo(BO->getLHS());
        addTo(BO->getRHS());
        return true;
    }

    virtual bool VisitBinLE(BinaryOperator *BO) {
        addTo(BO->getLHS());
        addTo(BO->getRHS());
        return true;
    }

    virtual bool VisitBinGE(BinaryOperator *BO) {
        addTo(BO->getLHS());
        addTo(BO->getRHS());
        return true;
    }

    /*
    virtual bool VisitBinEQ(BinaryOperator *BO) {
        addTo(BO->getLHS());
        addTo(BO->getRHS());
        return true;
    }

    virtual bool VisitBinNE(BinaryOperator *BO) {
        addTo(BO->getLHS());
        addTo(BO->getRHS());
        return true;
    }
    */

    std::set<std::string> getResult() {
        return res;
    }
};

std::set<std::string> getPassedConstantHelper(ASTContext *ast, Stmt *S) {
    IfStmt *IFS = llvm::dyn_cast<IfStmt>(S);
    if (!IFS)
        return std::set<std::string>();
    ConstantCondVisitor V(ast);
    V.TraverseStmt(IFS->getCond());
    return V.getResult();
}

class ConditionSynthesisTester : public BasicTester {
    typedef std::map<unsigned long, std::vector<unsigned long> > BranchRecordTy;
    typedef std::map<unsigned long, std::vector<std::vector<long long> > > ValueRecordTy;
    std::vector<ExprFillInfo> infos;
    std::map<unsigned long, ValueRecordTy> valueRecords;
    std::map<unsigned long, BranchRecordTy> branchRecords;
    bool full_synthesis;
    unsigned long post_cnt;

    long long getConditionIndex(const RepairCandidate &candidate) {
        const std::vector<RepairAction> &a = candidate.actions;
        // We identify the part we can use condition synthesizer, for the rest
        // we just brute search.
        long long condition_idx = -1;
        for (size_t i = 0; i < a.size(); i++)
            if (a[i].kind == RepairAction::ExprMutationKind)
                if (a[i].tag == RepairAction::CondTag) {
                    condition_idx = i;
                    break;
                }
        return condition_idx;
    }

    virtual clang::Expr* getFillExpr(size_t id) {
        long long condition_idx = getConditionIndex(candidates[id]);
        ExprFillInfo &tmp = infos[condition_idx];
        return tmp[condition_idx];
    }

    std::vector<unsigned long> parseBranchRecord() {
        std::vector<unsigned long> res;
        res.clear();
        FILE *f = fopen(ISNEG_TMPFILE, "r");
        //llvm::errs() << "New code\n" << new_code << "\n";
        if (!f) {
            outlog_printf(3, "Not caught by the negative case, give up!\n");
            //DEBUG(fprintf(stderr, "Not caught by the negative case, give up!\n"));
            //llvm::errs() << tmp_passed.size() << "\n";
            //assert(0);
            return res;
        }
        unsigned long n;
        int ret = fscanf(f, "%lu", &n);
        // FIXME: this is hacky!
        if (ret != 1) {
            fclose(f);
            return res;
        }
        for (size_t i = 0; i < n; i++) {
            unsigned long tmp;
            int ret = fscanf(f, "%lu", &tmp);
            // FIXME: something wierd, we get out!
            if (ret != 1) {
                fclose(f);
                return std::vector<unsigned long>();
            }
            res.push_back(tmp);
        }
        fclose(f);
        return res;
    }

    void writeBranchRecordTerminator() {
        FILE*f = fopen(ISNEG_TMPFILE, "a");
        fprintf(f, " 0");
        fclose(f);
    }

    void writeBranchRecord(const std::map<unsigned long, std::vector<unsigned long> > &negative_records, unsigned long idx) {
        FILE *f = fopen(ISNEG_TMPFILE, "w");
        std::map<unsigned long, std::vector<unsigned long> >::const_iterator fit = negative_records.find(idx);
        assert( fit != negative_records.end() );
        const std::vector<unsigned long> &tmp_vec = fit->second;
        fprintf(f, "%lu", (unsigned long)tmp_vec.size());
        for (size_t i = 0; i < tmp_vec.size(); i++)
            fprintf(f, " %lu", tmp_vec[i]);
        fprintf(f, "\n");
        fclose(f);
    }

    bool testNegativeCases(const BenchProgram::EnvMapTy &env,
            std::map<unsigned long, std::vector<unsigned long> > &negative_records) {
        negative_records.clear();
        // First going to make sure it passes all negative cases
        for (TestCaseSetTy::iterator case_it = negative_cases.begin();
                case_it != negative_cases.end(); ++case_it) {
            // OK, we are going to try 10 times for different path combination before
            // we give up!
            size_t it_cnt = 0;
            BenchProgram::EnvMapTy testEnv = env;
            testEnv.insert(std::make_pair("IS_NEG", "1"));
            testEnv.insert(std::make_pair("NEG_ARG", "1"));
            testEnv.insert(std::make_pair("TMP_FILE", ISNEG_TMPFILE));
            int ret = system((std::string("rm -rf ") + ISNEG_TMPFILE).c_str());
            assert( ret == 0);
            outlog_printf(5, "Testing %lu (with abstract condition)\n", *case_it);
            bool passed = false;
            while (it_cnt < 10) {
                outlog_printf(5, "Iteration %lu\n", it_cnt);
                //llvm::errs() << "Testing iteration: " << it_cnt << "\n";
                passed = P.test(std::string("src"), *case_it, testEnv, false);
                std::vector<unsigned long> tmp_v = parseBranchRecord();
                writeBranchRecordTerminator();
                for (size_t i = 0; i < tmp_v.size(); i++)
                    outlog_printf(5, "Branch %lu: %lu\n", i, tmp_v[i]);
                // We hit some strange error, we just assume we cannot pass this case
                if (tmp_v.size() == 0) passed = false;
                if (passed) {
                    outlog_printf(5, "Passed in iteration!\n");
                    negative_records[*case_it] = tmp_v;
                    break;
                }
                bool has_zero = false;
                for (size_t i = 0; i < tmp_v.size(); i++)
                    if (tmp_v[i] == 0) {
                        has_zero = true;
                        break;
                    }
                if (!has_zero) break;
                it_cnt ++;
            }
            // We will going to try all 1 before we finally give up this case
            if (!passed) {
                testEnv = env;
                testEnv.insert(std::make_pair("IS_NEG", "1"));
                testEnv.insert(std::make_pair("NEG_ARG", "0"));
                testEnv.insert(std::make_pair("TMP_FILE", ISNEG_TMPFILE));
                int ret = system((std::string("rm -rf ") + ISNEG_TMPFILE).c_str());
                assert( ret == 0);
                passed = P.test(std::string("src"), *case_it, testEnv, false);
                if (passed) {
                    std::vector<unsigned long> tmp_v = parseBranchRecord();
                    // FIXME: strange error in wireshark, we just ignore right now
                    if (tmp_v.size() == 0) {
                        outlog_printf(0, "Strange error or non-deterministic behavior!\n");
                        return false;
                    }
                    assert(tmp_v.size() != 0);
                    negative_records[*case_it] = tmp_v;
                    for (size_t i = 0; i < tmp_v.size(); i++)
                        outlog_printf(5, "Log %lu %lu\n", i, tmp_v[i]);
                }
                else {
                    // Still failed, we are going to give up
                    return false;
                }
            }
        }
        outlog_printf(2, "Passed Negative Cases wiht CondTestder!\n");
        return true;
    }

    void parseValueRecord(std::vector<std::vector<long long> > &vec, size_t expect_size) {
        vec.clear();
        FILE* f = fopen(ISNEG_RECORDFILE, "r");
        // Did not hit the condition, so it is an empty set
        if (f == NULL)
            return;
        bool over = false;
        while (!over) {
            std::vector<long long> v;
            v.clear();
            unsigned long n;
            int ret = fscanf(f, "%lu", &n);
            if (ret != 1) {
                over = true;
                break;
            }
            assert( n == expect_size);
            for (size_t i = 0; i < n; i++) {
                unsigned long tmp;
                ret = fscanf(f, "%lu", &tmp);
                assert(ret == 1);
                v.push_back(tmp);
            }
            vec.push_back(v);
        }
        fclose(f);
    }

    bool collectValues(const BenchProgram::EnvMapTy &env, const RepairCandidate &candidate,
            std::map<unsigned long, std::vector<unsigned long> > &negative_records,
            std::map<unsigned long, std::vector<std::vector<long long> > > &caseVMap) {
        size_t condition_idx = getConditionIndex(candidate);
        const ExprListTy &exps = candidate.actions[condition_idx].candidate_atoms;
        caseVMap.clear();
        // We first deal with the negative cases
        for (TestCaseSetTy::iterator tit = negative_cases.begin();
                tit != negative_cases.end(); ++tit) {
            BenchProgram::EnvMapTy testEnv = env;
            testEnv.insert(std::make_pair("IS_NEG", "RECORD1"));
            testEnv.insert(std::make_pair("NEG_ARG", ISNEG_TMPFILE));
            testEnv.insert(std::make_pair("TMP_FILE", ISNEG_RECORDFILE));
            //FIXME: It triggers non-deterministic things, get out!
            if (negative_records.find(*tit) == negative_records.end()) {
                fprintf(stderr, "Collect value failed on case %lu!\n", *tit);
                return false;
            }
            writeBranchRecord(negative_records, *tit);
            std::string cmd = std::string("rm -rf ") + ISNEG_RECORDFILE;
            int ret = system(cmd.c_str());
            assert( ret == 0);
            bool passed = P.test(std::string("src"), *tit, testEnv, false);
            // FIXME: It triggers non-deterministic things, just
            // get out
            if (!passed) {
                fprintf(stderr, "Collect value failed on case %lu!\n", *tit);
                return false;
            }
            // We are going to parse neg.out to get result
            caseVMap[*tit].clear();
            parseValueRecord(caseVMap[*tit], exps.size());
        }
        // Then we deal with positive cases
        for (TestCaseSetTy::iterator tit = positive_cases.begin();
                tit != positive_cases.end(); ++tit) {
            BenchProgram::EnvMapTy testEnv = env;
            testEnv.insert(std::make_pair("IS_NEG", "RECORD0"));
            testEnv.insert(std::make_pair("TMP_FILE", ISNEG_RECORDFILE));
            std::string cmd = std::string("rm -rf ") + ISNEG_RECORDFILE;
            int ret = system(cmd.c_str());
            assert( ret == 0);
            bool passed = P.test(std::string("src"), *tit, testEnv, false);
            caseVMap[*tit].clear();
            // XXX: This may happen because record takes more time, and it
            // makes the positive case to time out we simply skip if it fails
            if (!passed) continue;
            parseValueRecord(caseVMap[*tit], exps.size());
        }
        return true;
    }

public:
    ConditionSynthesisTester(BenchProgram &P, bool learning, SourceContextManager &M, bool full_synthesis):
        BasicTester(P, learning, M, false),
        infos(), full_synthesis(full_synthesis) { post_cnt = 0; }

    virtual bool canHandle(const RepairCandidate &candidate) {
        return getConditionIndex(candidate) != -1;
    }

    virtual std::vector<unsigned long> preprocess(const RepairCandidate &candidate) {
        outlog_printf(2, "[%llu] Preprocess the following candidate with CondTester:\n%s\n", get_timer(),
                candidate.toString(M).c_str());
        // We identify the part we can use condition synthesizer, for the rest
        // we just brute search.
        long long condition_idx = getConditionIndex(candidate);
        assert(condition_idx != -1);
        // We are going to create a set of binding ExprFillInfos
        std::set<ExprFillInfo> the_infos = enumerateExprBindings(M, candidate, condition_idx);
        std::vector<unsigned long> res;
        res.clear();
        for (std::set<ExprFillInfo>::iterator it = the_infos.begin(); it != the_infos.end();
                ++it) {
            ExprFillInfo efi = *it;
            CodeRewriter R(M, candidate, &efi);
            std::map<std::string, std::vector<std::string> > a_code = R.getCodeSegments();
            std::map<std::string, std::vector<std::string> > a_patch = R.getPatches();
            {
                outlog_printf(2, "[%llu] CondTester, a patch instance with id %lu:\n", get_timer(),
                        codes.size());
                out_codes(a_code, a_patch);
            }
            candidates.push_back(candidate);
            codes.push_back(a_code);
            patches.push_back(a_patch);
            infos.push_back(*it);
            res.push_back((unsigned long)candidates.size() - 1);
        }
        return res;
    }

    virtual bool test(const BenchProgram::EnvMapTy &env, unsigned long id) {
        {
            outlog_printf(2, "[%llu] CondTester, Testing instance id %lu:\n", get_timer(), id);
            out_codes(codes[id], patches[id]);
        }
        // We first need to find the flip combination that will make it passes each
        // negative cases, and we store it to negative_records
        std::map<unsigned long, std::vector<unsigned long> > negative_records;
        outlog_printf(3, "Testing negative cases!\n");
        if (!testNegativeCases(env, negative_records)) {
            codes[id].clear();
            patches[id].clear();
            return false;
        }
        outlog_printf(3, "Testing positive cases!\n");
        if (!BasicTester::testPositiveCases(env)) {
            codes[id].clear();
            patches[id].clear();
            return false;
        }
        // Then we need to collect the variable values at the expr, we store it into
        // this caseVMap
        outlog_printf(3, "Collect values for post processing!\n");
        std::map<unsigned long, std::vector<std::vector<long long> > > caseVMap;
        if (!collectValues(env, candidates[id], negative_records, caseVMap)) {
            codes[id].clear();
            patches[id].clear();
            return false;
        }
        valueRecords[id] = caseVMap;
        branchRecords[id] = negative_records;
        outlog_printf(2, "[%llu] Passed!\n", get_timer());
        return true;
    }

    virtual void dumpStat() {
        outlog_printf(0, "Total cnt of passed cond schemas: %lu\n", post_cnt);
        outlog_printf(0, "Total cnt of cond schemas: %lu\n", codes.size());
    }

    virtual std::map<NewCodeMapTy, double> getResults(unsigned long id) {
        post_cnt ++;
        {
            outlog_printf(2, "CondTester, Postprocessing instance id %lu:\n", id);
            out_codes(codes[id], patches[id]);
        }
        BranchRecordTy &negative_records = branchRecords[id];
        ValueRecordTy &caseVMap = valueRecords[id];
        RepairCandidate candidate = candidates[id];
        long long condition_idx = getConditionIndex(candidate);
        ASTContext *ast = M.getSourceContext(candidate.actions[condition_idx].loc.filename);
        ExprListTy &exps = candidates[id].actions[condition_idx].candidate_atoms;
        // We are going to do the synthesize, and we recompile everything we tried to recompile
        // FIXME: This is some really shitty code
        std::vector<Expr*> candidateExprs;
        if (learning)
            candidateExprs = synthesizeResult(exps, negative_records, caseVMap,
                negative_cases, positive_cases, ast);
        else
            candidateExprs = synthesizeResultSPR(exps, negative_records, caseVMap,
                negative_cases, positive_cases, ast);
        std::map<NewCodeMapTy, double> res_set;
        res_set.clear();
        bool passed_constant = false;
        double passed_constant_score = -1e20;
        std::set<std::string> helper;
        helper.clear();
        int passed_cnt = 0;
        patch_explored += candidateExprs.size();
        for (size_t i = 0; i < candidateExprs.size(); i++) {
            if (the_timeout_limit != 0)
                if (get_timer() > the_timeout_limit) {
                    outlog_printf(1, "[%llu] Timeout! Limit is %llu\n", get_timer(), the_timeout_limit);
                    break;
                }
            Expr* new_expr = candidateExprs[i];
            ExprFillInfo cur_info = infos[id];
            cur_info[condition_idx] = new_expr;
            double score = computeFinalScore(learning, M, candidate, id, new_expr);
            if (learning) {
                if (!isZeroConstantExpr(stripParenAndCast(new_expr)) && (stmtToString(*ast, new_expr).find("len") != std::string::npos))
                    score -= 0.7;
                if (passed_constant) {
                    bool found_it = false;
                    std::string stmtStr = stmtToString(*ast, stripParenAndCast(new_expr));
                    for (std::set<std::string>::iterator it = helper.begin(); it != helper.end(); it++)
                        if (stmtStr.find(*it) == 0) {
                            size_t idx = it->size();
                            if (stmtStr.size() > idx + 2)
                                if ((stmtStr[idx] == ' ') && (stmtStr[idx + 2] == '=')) {
                                    found_it = true;
                                    break;
                                }
                        }
                    if (found_it) {
                        outlog_printf(2, "Going to try %s even with passed constant!\n", stmtStr.c_str());
                    }
                    else {
                        outlog_printf(2, "Rejected %s because of passed constant!\n", stmtStr.c_str());
                        if (passed_constant_score - 0.1 + 1e-4 * score < score)
                            score = passed_constant_score - 0.1 + 1e-4 * score;
                    }
                }
            }
            if (!full_synthesis) {
                if (learning) {
                    if (found_score >= score && !isIntegerConstant(new_expr))
                        continue;
                }
                else if (found_score >= score)
                    continue;
            }
            CodeRewriter R(M, candidate, &cur_info);
            NewCodeMapTy code = R.getCodes();
            BenchProgram::EnvMapTy buildEnv;
            buildEnv.clear();
            if (ForCPP.getValue())
                buildEnv["COMPILE_CMD"] = "clang++";
            else
                buildEnv["COMPILE_CMD"] = GCC_CMD;
            outlog_printf(2, "Trying a synthesis expr %s\n", stmtToString(*ast, new_expr).c_str());
            bool build_succ = P.buildWithRepairedCode(CLANG_TEST_WRAP, buildEnv, code);
            if (!build_succ) {
                outlog_printf(3, "Build failed when synthesizing!\n");
                continue;
            }
            TestCaseSetTy passed;
            outlog_printf(3, "Verifing Negative cases!\n");
            passed = P.testSet("src", negative_cases, std::map<std::string, std::string>());
            if (passed != negative_cases) {
                outlog_printf(3, "Not passed!\n");
                continue;
            }
            outlog_printf(3, "Verifying positive cases\n");
            bool passed_pos = testPositiveCases(std::map<std::string, std::string>());
            //passed = P.testSet("src", positive_cases, std::map<std::string, std::string>());
            if (!passed_pos) {
                outlog_printf(3, "Not passed!\n");
                continue;
            }
            outlog_printf(2, "[%llu] Passed!\n", get_timer());
            passed_cnt ++;
            if (full_synthesis && !learning)
                // OK, i don't want to explain this. It is just a hacky fix to make the experiment checking
                // easier. The first passed will come out first if possible.
                res_set.insert(std::make_pair(cleanUpCode(code), score - 1e-3 * passed_cnt));
            else
                res_set.insert(std::make_pair(cleanUpCode(code), score));
            if (DumpPassedCandidate.getValue() != "") {
                assert(candidate.actions.size() > 0);
                Expr *E1 = NULL;
                if (new_expr) {
                    E1 = stripParenAndCast(new_expr);
                    if (isIntegerConstant(E1))
                        E1 = NULL;
                    if (E1) {
                        BinaryOperator *BO = llvm::dyn_cast<BinaryOperator>(E1);
                        if (BO)
                            E1 = BO->getLHS();
                    }
                }
                dumpCandidate(M, candidates[id], E1, score);
            }
            if (learning)
                if (isIntegerConstant(new_expr)) {
                    passed_constant = true;
                    passed_constant_score = score;
                    helper = getPassedConstantHelper(ast, candidate.actions[condition_idx].loc.stmt);
                    outlog_printf(2, "Passed constant expr!\n");
                    for (std::set<std::string>::iterator it = helper.begin(); it != helper.end(); ++it)
                        outlog_printf(2, "Still allow %s.\n", it->c_str());
                }
            if (found_score < score) {
                found_score = score;
                outlog_printf(2, "Passed with updated best score %lf\n", found_score);
            }
        }
        if (res_set.size() != 0) {
            valueRecords.erase(id);
            branchRecords.erase(id);
            return res_set;
        }
        // FIXME: This is too hacky, I hate this!
        double score = computeFinalScore(learning, M, candidate, id, NULL);
        if (found_score < score) {
            CodeSegTy codeSegs = codes[id];
            PatchListTy patch = patches[id];
            NewCodeMapTy new_code = combineCode(codeSegs, patch);
            std::string src_file = candidate.actions[condition_idx].loc.src_file;
            outlog_printf(3, "Initial synthesize failed, final attempt\n");
            // We are going to loose / tight the condition with existing
            // clause as the final attempt
            assert( new_code.count(src_file) != 0);
            std::set<std::string> codes = replaceIsNegWithClause(new_code[src_file]);
            unsigned long cnt = 0;
            patch_explored += codes.size();
            for (std::set<std::string>::iterator sit = codes.begin();
                    sit != codes.end(); ++sit) {
                cnt ++;
                outlog_printf(3, "Final attempt %lu/%lu with expr %s\n", cnt, codes.size(),
                        sit->c_str());
                new_code[src_file] = *sit;
                TestCaseSetTy passed;
                BenchProgram::EnvMapTy buildEnv;
                buildEnv.clear();
                if (ForCPP.getValue())
                    buildEnv["COMPILE_CMD"] = "clang++";
                else
                    buildEnv["COMPILE_CMD"] = GCC_CMD;
                bool build_succ = P.buildWithRepairedCode(CLANG_TEST_WRAP, buildEnv, new_code);
                if (!build_succ) {
                    outlog_printf(3, "Build failed\n");
                    continue;
                }
                outlog_printf(3, "Trying Negative cases!\n");
                passed = P.testSet("src", negative_cases, std::map<std::string, std::string>());
                if (passed == negative_cases) {
                    outlog_printf(3, "Trying Positive cases!\n");
                    passed = P.testSet("src", positive_cases, std::map<std::string, std::string>());
                    if (passed == positive_cases) {
                        outlog_printf(2, "[%llu] Passed!\n", get_timer());
                        if (DumpPassedCandidate.getValue() != "")
                            dumpCandidate(M, candidate, NULL, score);
                        valueRecords.erase(id);
                        branchRecords.erase(id);
                        if (found_score < score) {
                            found_score = score;
                            outlog_printf(2, "Updated best score %lf\n", found_score);
                        }
                        return singleResult(cleanUpCode(new_code), score);
                    }
                }
            }
        }
        outlog_printf(2, "Postprocessing failed!\n");
        valueRecords.erase(id);
        branchRecords.erase(id);
        return std::map<NewCodeMapTy, double>();
    }
};

class TestBatcher {
    BenchProgram &P;
    bool naive;
    bool learning;
    FeatureParameter *FP;

    struct CandidateEntry {
        RepairCandidate rc;
        BasicTester *T;
        unsigned long id;

        CandidateEntry(const RepairCandidate &rc, BasicTester *T, unsigned long id):
            rc(rc), T(T), id(id) {}
    };

    typedef std::map<CodeSegTy, std::vector<CandidateEntry> > CandidateMapTy;
    std::map<NewCodeMapTy, double> res;
    std::vector<RepairCandidate> succCandidates;
    CandidateMapTy candidateMap;
    size_t cur_size;
    unsigned long total_cnt;


    std::map<NewCodeMapTy, double> singleTest(const CodeSegTy &codeSegs, const CodeSegTy &patches,
            BasicTester *T, unsigned long id) {
        BenchProgram::EnvMapTy buildEnv;
        buildEnv.clear();
        if (ForCPP.getValue())
            buildEnv["COMPILE_CMD"] = "clang++";
        else
            buildEnv["COMPILE_CMD"] = GCC_CMD;
        bool build_succ = P.buildWithRepairedCode(CLANG_TEST_WRAP, buildEnv,
                combineCode(codeSegs, patches));
        if (!build_succ) {
            outlog_printf(2, "Single building for Tester %p id %lu failed as well!\n",
                    T, id);
            return std::map<NewCodeMapTy, double>();
        }
        bool ret = T->test(BenchProgram::EnvMapTy(), id);
        if (ret)
            return T->getResults(id);
        else
            return std::map<NewCodeMapTy, double>();
    }

    void doTest(const CodeSegTy &codeSegs) {
        if (the_timeout_limit != 0)
            if (get_timer() > the_timeout_limit) {
                outlog_printf(1, "[%llu] Timeout! Limit is %llu\n", get_timer(), the_timeout_limit);
                return;
            }
        outlog_printf(2, "a batched test job starts!\n");
        // We are going to build a single batched code for this,
        // this saves a lot of compile time for testing!
        std::vector<CandidateEntry> &tmp = candidateMap[codeSegs];
        cur_size -= tmp.size();
        std::vector<PatchListTy> tmp_patches;
        tmp_patches.clear();
        for (size_t i = 0; i < tmp.size(); i++) {
            BasicTester *T = tmp[i].T;
            tmp_patches.push_back(T->getPatches(tmp[i].id));
            tot_explored_templates += tmp[i].rc.getCandidateAtoms().size();
            patch_explored += tmp[i].rc.getCandidateAtoms().size();
            outlog_printf(0, "The number of explored templates: %lu\n", tot_explored_templates);
        }
        std::map<std::string, std::string> codes = mergeCode(codeSegs, tmp_patches);
        {
            outlog_printf(4, "Building merged code:\n");
            for (NewCodeMapTy::iterator it = codes.begin(); it != codes.end(); ++ it) {
                outlog_printf(4, "src_file: %s\n", it->first.c_str());
                outlog_printf(4, "full src: %s\n", it->second.c_str());
            }
        }
        BenchProgram::EnvMapTy buildEnv;
        buildEnv.clear();
        if (ForCPP.getValue())
            buildEnv["COMPILE_CMD"] = "clang++";
        else
            buildEnv["COMPILE_CMD"] = GCC_CMD;
        bool build_succ = P.buildWithRepairedCode(CLANG_TEST_WRAP, buildEnv, codes);
        if (build_succ) {
            outlog_printf(2, "Merged code building succ, going to invoke tester!\n");
            // We then invoke these testers they all share this same built instance
            std::vector<std::pair<BasicTester*, unsigned long> > succ_list;
            std::vector<RepairCandidate> c_list;
            succ_list.clear();
            c_list.clear();
            for (size_t i = 0; i < tmp.size(); i++) {
                BasicTester *T = tmp[i].T;
                BenchProgram::EnvMapTy testEnv;
                testEnv.clear();
                std::ostringstream sout;
                sout << i;
                testEnv["MUTANT_ID"] = sout.str();
                bool ret = T->test(testEnv, tmp[i].id);
                if (ret) {
                    succ_list.push_back(std::make_pair(T, tmp[i].id));
                    c_list.push_back(tmp[i].rc);
                }
            }
            // We then need to invoke the post processing of these successive runs to
            // get the results, we split this with the main test because this part may
            // involve build the bench program again.
            for (size_t i = 0; i < succ_list.size(); i++) {
                std::map<NewCodeMapTy, double> code_set = succ_list[i].first->getResults(succ_list[i].second);
                for (std::map<NewCodeMapTy, double>::iterator it = code_set.begin();
                        it != code_set.end(); it++) {
                    NewCodeMapTy code = it->first;
                    double res_score = it->second;
                    if (res.count(code) == 0)
                        res.insert(std::make_pair(code, res_score));
                    else if (res[code] < res_score)
                        res[code] = res_score;
                    succCandidates.push_back(c_list[i]);
                }
            }
        }
        else {
            outlog_printf(2, "Merged code building failed! Going to build saperately!\n");
            // We have to fail back to naive way, build them saperately
            for (size_t i = 0; i < tmp.size(); i++) {
                BasicTester *T = tmp[i].T;
                std::map<NewCodeMapTy, double> code_set = singleTest(codeSegs, tmp_patches[i], T, tmp[i].id);
                for (std::map<NewCodeMapTy, double>::iterator it = code_set.begin();
                        it != code_set.end(); it++) {
                    NewCodeMapTy code = it->first;
                    double res_score = it->second;
                    if (res.count(code) == 0)
                        res.insert(std::make_pair(code, res_score));
                    else if (res[code] < res_score)
                        res[code] = res_score;
                    succCandidates.push_back(tmp[i].rc);
                }
            }
        }
        candidateMap.erase(codeSegs);
    }
public:
    TestBatcher(BenchProgram &P, bool naive,
            bool learning, FeatureParameter *FP):
        P(P), naive(naive), learning(learning && !naive), FP(FP), res(), succCandidates(), candidateMap(), cur_size(0),
    total_cnt(0) { }

    // This is a lazy test routine, we are only going to decode it without
    // actually doing the test in the most of the time
    void test(const RepairCandidate &candidate, BasicTester* T) {
        std::vector<unsigned long> ids = T->preprocess(candidate);
        total_cnt += ids.size();
        outlog_printf(2, "Spawn %lu instances, now Total %lu\n", (unsigned long)ids.size(), total_cnt);
        for (size_t i = 0; i < ids.size(); i++) {
            CodeSegTy codeSegs = T->getCodeSegs(ids[i]);
            PatchListTy patches = T->getPatches(ids[i]);
            if (canMerge(codeSegs, patches) && (!naive)) {
                if (candidateMap.count(codeSegs) == 0)
                    candidateMap[codeSegs].clear();
                candidateMap[codeSegs].push_back(CandidateEntry(candidate, T, ids[i]));
                cur_size ++;
                if (candidateMap[codeSegs].size() >= BATCH_CAP)
                    doTest(codeSegs);
            }
            else {
                tot_explored_templates += candidate.getCandidateAtoms().size();
                patch_explored += candidate.getCandidateAtoms().size();
                outlog_printf(0, "The number of explored templates: %lu\n", tot_explored_templates);
                std::map<NewCodeMapTy, double> code_set = singleTest(codeSegs, patches, T, ids[i]);
                for (std::map<NewCodeMapTy, double>::iterator it = code_set.begin();
                        it != code_set.end(); it++) {
                    NewCodeMapTy code = it->first;
                    double res_score = it->second;
                    if (res.count(code) == 0)
                        res.insert(std::make_pair(code, res_score));
                    else if (res[code] < res_score)
                        res[code] = res_score;
                    succCandidates.push_back(candidate);
                }
            }
        }
    }

    bool hasResult() {
        return res.size() != 0;
    }

    std::vector<std::pair<NewCodeMapTy, double> > getResults() {
        std::vector<std::pair<NewCodeMapTy, double> > tmp;
        tmp.clear();
        for (std::map<NewCodeMapTy, double>::iterator it = res.begin(); it != res.end(); it++)
            tmp.push_back(std::make_pair(it->first, it->second));
        if (tmp.size() > 0) {
            for (size_t i = 0; i < tmp.size() - 1; i++)
                for (size_t j = i + 1; j < tmp.size(); j++)
                    if (tmp[i].second < tmp[j].second)
                        std::swap(tmp[i], tmp[j]);
        }
        return tmp;
    }

    void sync() {
        std::vector<CodeSegTy> tmp;
        tmp.clear();
        for (CandidateMapTy::iterator it = candidateMap.begin();
                it != candidateMap.end(); ++it)
            tmp.push_back(it->first);
        for (size_t i = 0; i < tmp.size(); ++i)
            doTest(tmp[i]);
    }

    size_t size() {
        return cur_size;
    }

    std::vector<RepairCandidate> getSuccCandidates() {
        return succCandidates;
    }
};

}

bool ExprSynthesizer::workUntil(size_t candidate_limit, size_t time_limit,
        ExprSynthesizerResultTy &res, bool full_synthesis, bool quit_with_any) {
    the_timeout_limit = this->timeout_limit;
    TestBatcher TB(P, naive, learning, FP);
    std::vector<BasicTester*> testers;
    testers.clear();
    testers.push_back(new ConditionSynthesisTester(P, learning, M, full_synthesis));
    testers.push_back(new StringConstTester(P, learning, M, naive));
    testers.push_back(new BasicTester(P, learning, M, naive));
    outlog_printf(2, "BasicTester pointer: %p\n", testers[2]);
    outlog_printf(2, "StringConstTester pointer: %p\n", testers[1]);
    outlog_printf(2, "CondTester pointer: %p\n", testers[0]);
    TestCache *cache = P.getTestCache();
    size_t cnt = 0;
    ExecutionTimer Timer;
    time_t last_sync = Timer.getSeconds();

    std::vector<std::pair<NewCodeMapTy, double> > collected_res;
    std::map<std::string, size_t> candidate_to_id;
    candidate_to_id.clear();
    collected_res.clear();
    unsigned long generate_min_id = 100000000;
    found_score = -1e20;
    // FIXME: we ignore time limit now, we will add back later
    while (q.size() > 0 && ((tested_cnt < candidate_limit) || (candidate_limit == 0))) {
        if (timeout_limit != 0)
            if (get_timer() > timeout_limit) {
                outlog_printf(1, "[%llu] Timeout! Limit is %llu\n", get_timer(), timeout_limit);
                break;
            }
        cnt ++;
        time_t now_t = Timer.getSeconds();
        if ((cnt % SYNC_CAP == 0) || (now_t - last_sync > SYNC_TIME_CAP)) {
            last_sync = now_t;
            outlog_printf(2, "Going to sync the batch tester, clear all existing tasks!\n");
            TB.sync();
        }
        if (TB.hasResult()) {
            TB.sync();
            std::vector<std::pair<NewCodeMapTy, double> > tmp = TB.getResults();
            if (tmp.size() > 0)
                if (found_score < tmp[0].second) {
                    found_score = tmp[0].second;
                    outlog_printf(1, "Updated best score result: %lf\n", found_score);
                }
            //collected_res.insert(collected_res.end(), tmp.begin(), tmp.end());
            std::vector<RepairCandidate> succs = TB.getSuccCandidates();
            for (size_t i = 0; i < succs.size(); i++) {
                cache->markSucc(succs[i].toString(M));
                unsigned long schema_id = candidate_to_id[succs[i].toString(M)];
                outlog_printf(1, "Generate a candidate with schema id: %lu\n", schema_id);
                if (generate_min_id > schema_id)
                    generate_min_id = schema_id;
            }
            ((ConditionSynthesisTester*)testers[0])->dumpStat();
            if (quit_with_any) {
                outlog_printf(1, "Quit-with-any flag on, just going to get out.");
                break;
            }
        }
        outlog_printf(2, "Counter: %lu\nBatcher Size:%lu\n", cnt, TB.size());
        RepairCandidateWithScore candidate_a_score = q.top();
        RepairCandidate candidate = candidate_a_score.first;
        if (candidate_a_score.second <= found_score) {
            outlog_printf(1, "The found score %lf is greater than current score %lf!\n", found_score, candidate_a_score.second);
            outlog_printf(1, "Terminate current session!\n");
            break;
        }
        q.pop();
        //FIXME: Diable cache for now, need to find a better way
        if (0)
            if (cache->isNotSucc(candidate.toString(M))) {
                outlog_printf(2, "Skip the following candidate based on cache:\n%s",
                        candidate.toString(M).c_str());
                continue;
            }
        cache->addCandidate(candidate.toString(M));
        tested_cnt ++;
        bool found = false;
        candidate_to_id[candidate.toString(M)] = cnt;
        for (size_t i = 0; i < testers.size(); i++)
            if (testers[i]->canHandle(candidate)) {
                TB.test(candidate, testers[i]);
                found = true;
                break;
            }
        if (!found) {
            outlog_printf(0, "Unable to handle a candidate:\n%s\n", candidate.toString(M).c_str());
            continue;
        }
    }
    TB.sync();
    if (TB.hasResult()) {
        std::vector<std::pair<NewCodeMapTy, double> > tmp = TB.getResults();
        collected_res.insert(collected_res.end(), tmp.begin(), tmp.end());
        std::vector<RepairCandidate> succs = TB.getSuccCandidates();
        for (size_t i = 0; i < succs.size(); i++) {
            cache->markSucc(succs[i].toString(M));
            unsigned long schema_id = candidate_to_id[succs[i].toString(M)];
            outlog_printf(1, "Generate a candidate with schema id: %lu\n", schema_id);
            if (generate_min_id > schema_id)
                generate_min_id = schema_id;
        }
        ((ConditionSynthesisTester*)testers[0])->dumpStat();
    }
    if (generate_min_id != 100000000)
        outlog_printf(1, "The first schema id that generates patch: %lu\n", generate_min_id);
    outlog_printf(0, "The total number of synthesis runs: %lu\n", tot_synthesis_run);
    outlog_printf(0, "The total number of concrete conds: %lu\n", tot_concrete_conds);
    outlog_printf(0, "The total number of explored concrete patches: %lu\n", patch_explored);
    //res.clear();
    for (size_t i = 0; i < collected_res.size(); i++)
        for (size_t j = i; j < collected_res.size(); j++)
            if (collected_res[i].second < collected_res[j].second)
                std::swap(collected_res[i], collected_res[j]);
    //for (size_t i = 0; i < collected_res.size(); i++)
    //    res.push_back(collected_res[i].first);
    res = collected_res;
    for (size_t i = 0; i < testers.size(); i++)
        delete testers[i];
    return res.size() != 0;
}
