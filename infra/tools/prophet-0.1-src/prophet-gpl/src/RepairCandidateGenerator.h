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
#include "ASTUtils.h"
#include "SourceContextManager.h"
#include <vector>
#include <queue>

namespace clang {
    class Stmt;
    class Expr;
}

typedef std::vector<clang::Stmt*> StmtListTy;
typedef std::vector<clang::Expr*> ExprListTy;

struct RepairAction {
    // tag = 1, means a statement level mutation
    // tag = 2, means a expr level mutation
    typedef enum {
        ReplaceMutationKind = 0,
        InsertMutationKind,
        InsertAfterMutationKind,
        ExprMutationKind
    } RepairActionKind;
    RepairActionKind kind;
    ASTLocTy loc;
    // It is a clang::Stmt or clang::Expr
    void *ast_node;
    // This will only be used for expr level mutations
    ExprListTy candidate_atoms;
    // This is a tag to indicate which subroutine created this
    // action
    typedef enum {
        InvalidTag = 0,
        CondTag,
        StringConstantTag,
    } ExprTagTy;
    ExprTagTy tag;

    RepairAction(const ASTLocTy &loc, RepairActionKind kind, clang::Stmt* new_stmt)
        : kind(kind), loc(loc), ast_node((void*)new_stmt),
        candidate_atoms(), tag(InvalidTag) { }

    RepairAction(const ASTLocTy &loc, clang::Expr* expr,
            const std::vector<clang::Expr*> &candidate_atoms)
        : kind(ExprMutationKind), loc(loc), ast_node((void*)expr),
        candidate_atoms(candidate_atoms), tag(CondTag) { }

/*    bool operator < (const RepairAction &a)  const {
        if (kind != a.kind)
            return kind < a.kind;
        else if (loc < a.loc)
            return true;
        else if (a.loc < loc)
            return false;
        else if (ast_node != a.ast_node)
            return ast_node < a.ast_node;
        else if (tag != a.tag)
            return tag < a.tag;
        else
            return candidate_atoms < a.candidate_atoms;
    }*/
};

struct RepairCandidate {
    std::vector<RepairAction> actions;
    // Below are required information to calculate the property
    // of the repair candidate
    typedef enum {
        TightenConditionKind = 0,
        LoosenConditionKind,
        GuardKind,
        SpecialGuardKind,
        IfExitKind,
        AddInitKind,
        ReplaceKind,
        ReplaceStringKind,
        AddAndReplaceKind
    } CandidateKind;
    CandidateKind kind;
    bool is_first; // start of a block? not including condition changes
    clang::Expr *oldRExpr, *newRExpr; // info for replace only
    // This should be the human localization score for learning
    // or the pre-fixed score if not using learning
    double score;
    std::map<clang::Expr*, double> scoreMap;
   /* size_t score;

    bool operator <(const RepairCandidate &a) const {
        if (score != a.score)
            return score < a.score;
        else if (actions.size() != a.actions.size())
            return actions.size() < a.actions.size();
        else {
            for (size_t i = 0; i < actions.size(); i++) {
                if (actions[i] < a.actions[i])
                    return true;
                if (a.actions[i] < actions[i])
                    return false;
            }
            return false;
        }
    }*/

    RepairCandidate(): actions(), kind(), is_first(false), oldRExpr(NULL), newRExpr(NULL), score(0), scoreMap() { }

    std::set<clang::Expr*> getCandidateAtoms() const {
        std::set<clang::Expr*> ret;
        ret.clear();
        ret.insert(NULL);
        for (size_t i = 0; i < actions.size(); i++)
            if (actions[i].kind == RepairAction::ExprMutationKind) {
                for (size_t j = 0; j < actions[i].candidate_atoms.size(); j++)
                    ret.insert(actions[i].candidate_atoms[j]);
                return ret;
            }
        return ret;
    }

    std::string toString(SourceContextManager &M) const;

    void dump() const;
};

class RepairCandidateGeneratorImpl;

typedef std::pair<RepairCandidate, double> RepairCandidateWithScore;

struct RepairComp {
    bool operator () (const RepairCandidateWithScore &a, const RepairCandidateWithScore &b) {
        return a.second < b.second;
    }
};

typedef std::priority_queue<RepairCandidateWithScore, std::vector<RepairCandidateWithScore>,
        RepairComp> RepairCandidateQueue;

class RepairCandidateGenerator {
    RepairCandidateGeneratorImpl *impl;
public:
    RepairCandidateGenerator(SourceContextManager &M, const std::string &file,
            const std::map<clang::Stmt*, unsigned long> &locs,
            bool naive, bool learning);

    void setFlipP(double GeoP);

    ~RepairCandidateGenerator();

    std::vector<RepairCandidate> run();
};
