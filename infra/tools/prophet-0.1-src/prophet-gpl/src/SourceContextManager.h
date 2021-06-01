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
#pragma once
#include <map>
#include <string>
#include <vector>
#include <set>
#include "Utils.h"
#include "ASTUtils.h"
#include "ErrorLocalizer.h"

#define IS_NEG_HANDLER "__is_neg"
#define UNKNOWN_HOOK "__abst_hole"

class LocalAnalyzer;
class BenchProgram;
class RepairCandidate;
class GlobalAnalyzer;

namespace clang {
    class ASTUnit;
    class ASTContext;
    class Stmt;
    class CallExpr;
    class Expr;
    class QualType;
};

struct InternalHandlerInfo {
    clang::Expr* abstract_cond;
    clang::Expr* abstract_hole;
    clang::Expr* sys_memset;
};

typedef std::vector<clang::Expr*> ExprListTy;

class SourceContextManager {
    std::map<std::string, std::unique_ptr<clang::ASTUnit> > unitMap;
    std::map<ASTLocTy, LocalAnalyzer*> localAnalyzerMap;
    std::map<std::string, std::string> codeMap;
    std::map<clang::ASTContext*, InternalHandlerInfo> internalHandlerMap;
    std::map<clang::ASTContext*, GlobalAnalyzer*> globalAnalyzerMap;
    // some hacky set to determine whether a statement pointer is new or existing
    std::set<clang::Stmt*> existing_stmts;
    std::vector<clang::Stmt*> StmtList;
    BenchProgram *P;
    // some hacky flag we need to pass to local analyzer, wth
    bool naive;

    void fetch(const std::string &file);

public:

    SourceContextManager() : P(NULL), naive(false) {
        unitMap.clear();
        localAnalyzerMap.clear();
        codeMap.clear();
        internalHandlerMap.clear();
        globalAnalyzerMap.clear();
        existing_stmts.clear();
    }

    SourceContextManager(BenchProgram &P, bool naive) : P(&P), naive(naive) {
        unitMap.clear();
        localAnalyzerMap.clear();
        codeMap.clear();
        internalHandlerMap.clear();
        globalAnalyzerMap.clear();
        existing_stmts.clear();
    }

    ~SourceContextManager();

    std::string newSourceFile(const std::string &projDir, const std::string &srcFile,
            const std::string &buildDir, const std::vector<std::string> &buildArgs);

    std::string getSourceCode(const std::string &src_file) {
        if (codeMap.count(src_file) == 0) {
            assert( P != NULL );
            fetch(src_file);
        }
        return codeMap[src_file];
    }

    clang::ASTContext *getSourceContext(const std::string &src_file);

    SourcePositionTy fixSourceLocation(const SourcePositionTy &s) {
        SourcePositionTy ret = s;
        std::string ext = get_ext(ret.expFilename);
        if ((ext == "c") || (ext == "cpp"))
            ret.expLine ++;
        return ret;
    }

    InternalHandlerInfo getInternalHandlerInfo(clang::ASTContext *ctxt) {
        assert(internalHandlerMap.count(ctxt) != 0);
        return internalHandlerMap[ctxt];
    }

    //void pushChanges(RepairCandidate &candidate);

    //void popChanges(RepairCandidate &candidate);

    LocalAnalyzer* getLocalAnalyzer(const ASTLocTy &loc);

    bool isNewStmt(clang::Stmt* s) {
        return existing_stmts.count(s) == 0;
    }

    // FIXME: This stupid shit should go somewhere else
    clang::Expr* getExprPlaceholder(clang::ASTContext *ctxt, clang::QualType QT);

    clang::Expr* getUnknownExpr(clang::ASTContext *ctxt, ExprListTy candidate_atoms);

    std::string cleanUpCode(const std::string &str);
};
