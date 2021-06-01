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
#include "Utils.h"
#include <string>
#include <vector>
#include <set>
#include <fstream>
#include <sstream>
#include <map>
#include <assert.h>
#include "llvm/Support/raw_ostream.h"

class BenchProgram;

struct SourcePositionTy {
    std::string expFilename;
    size_t expLine;
    size_t expColumn;
    std::string spellFilename;
    size_t spellLine;
    size_t spellColumn;

    SourcePositionTy():
    expFilename(""), expLine(0), expColumn(0),
    spellFilename(""), spellLine(0), spellColumn(0) { }

    SourcePositionTy(const std::string &filename, size_t line_number):
    expFilename(filename), expLine(line_number), expColumn(0),
    spellFilename(""), spellLine(0), spellColumn(0) { }

    ~SourcePositionTy() { }

    bool operator < (const SourcePositionTy &a) const {
        if (expFilename != a.expFilename)
            return expFilename < a.expFilename;
        else if (expLine != a.expLine)
            return expLine < a.expLine;
        else if (expColumn != a.expColumn)
            return expColumn < a.expColumn;
        else if (spellFilename != a.spellFilename)
            return spellFilename < a.spellFilename;
        else if (spellLine != a.spellLine)
            return spellLine < a.spellLine;
        else
            return spellColumn < a.spellColumn;
    }

    std::string toString() const {
        std::ostringstream sout;
        sout << expFilename << " " << expLine << " " << expColumn << " "
            << spellFilename << " " << spellLine << " " << spellColumn;
        return sout.str();
    }
};

std::ostream & operator << (std::ostream &os, const SourcePositionTy &a);

llvm::raw_ostream & operator << (llvm::raw_ostream &os, const SourcePositionTy &a);

std::istream & operator >> (std::istream &os, SourcePositionTy &a);

class LocationIndex {
    std::map<SourcePositionTy, size_t> loc_map;
    std::vector<SourcePositionTy> loc_v;
    size_t old_cnt;
    std::string filename;
public:
    LocationIndex(const std::string &filename): filename(filename) {
        std::ifstream fin(filename.c_str(), std::ifstream::in);
        if (!fin.is_open()) {
            std::ofstream fout(filename.c_str(), std::ofstream::out);
            assert(fout.is_open());
            fout.close();
            loc_map.clear();
            loc_v.clear();
            old_cnt = 0;
        }
        else {
            std::string line;
            while (getline(fin, line)) {
                if (line == "") break;
                std::istringstream sin(line);
                SourcePositionTy loc;
                sin >> loc.expFilename >> loc.expLine >> loc.expColumn
                    >> loc.spellFilename >> loc.spellLine >> loc.spellColumn;
                loc_map.insert(std::make_pair(loc, loc_v.size()));
                loc_v.push_back(loc);
            }
            fin.close();
            old_cnt = loc_v.size();
        }
    }

    size_t getIndexNo(const std::string &expFilename, size_t expLine, size_t expColumn,
            const std::string &spellFilename, size_t spellLine, size_t spellColumn) {
        SourcePositionTy loc;
        loc.expFilename = expFilename;
        loc.expLine = expLine;
        loc.expColumn = expColumn;
        loc.spellFilename = spellFilename;
        loc.spellLine = spellLine;
        loc.spellColumn = spellColumn;
        if (loc_map.count(loc) == 0) {
            loc_map.insert(std::make_pair(loc, loc_v.size()));
            loc_v.push_back(loc);
        }
        return loc_map[loc];
    }

    SourcePositionTy getProfileLocation(size_t id) {
        //assert(id < loc_v.size() );
        return loc_v[id];
    }

    void writeBack() {
        std::ofstream fout(filename.c_str(), std::ofstream::app);
        assert( fout.is_open() );
        for (size_t i = old_cnt; i < loc_v.size(); i++)
            fout << loc_v[i].expFilename << " " << loc_v[i].expLine << " " << loc_v[i].expColumn << " "
                << loc_v[i].spellFilename << " " << loc_v[i].spellLine << " " << loc_v[i].spellColumn << "\n";
        fout.close();
    }
};

class ErrorLocalizer {
public:
    virtual std::vector<SourcePositionTy> getCandidateLocations() = 0;

    virtual void printResult(const std::string &outfile) = 0;

    virtual ~ErrorLocalizer() { };
};

// This is a naive error localizer because we cheat!
class NaiveErrorLocalizer : public ErrorLocalizer {
    BenchProgram &P;
    typedef std::set<size_t> TestCaseSetTy;
    std::vector<SourcePositionTy> candidateLocations;
public:
    NaiveErrorLocalizer(BenchProgram &P);

    virtual std::vector<SourcePositionTy> getCandidateLocations() {
        return candidateLocations;
    }

    virtual void printResult(const std::string &outfile) {
        std::ofstream fout(outfile.c_str(), std::ofstream::out);
        assert(fout.is_open());
        for (size_t i = 0; i < candidateLocations.size(); i++) {
            std::string filename = candidateLocations[i].expFilename;
            size_t line_number = candidateLocations[i].expLine;
            fout << filename << ":" << line_number << "\n";
        }
        fout.close();
    }
    virtual ~NaiveErrorLocalizer() { }
};
