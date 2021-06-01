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
#include "FeatureVector.h"
#include <string>
#include <vector>
#include <algorithm>

class FeatureParameter : public std::vector<double> {
public:
    FeatureParameter(): std::vector<double>() { }

    void resetZero(size_t newS) {
        resize(newS);
        for (size_t i = 0; i < newS; i++)
            at(i) = 0;
    }

    template<typename T>
    void dump(T& out, double epsilon = 1e-6) const {
        std::vector<std::pair<double, std::string> > tmp;
        tmp.clear();
        for (size_t i = 0; i < size(); i ++)
            tmp.push_back(std::make_pair(at(i), FeatureVector::fidToString(i)));
        std::sort(tmp.begin(), tmp.end());
        for (size_t i = 0; i < tmp.size(); i++)
            if (fabs(tmp[i].first) > epsilon)
                out << tmp[i].second << ": " << tmp[i].first << "\n";
    }

    double dotProduct(const FeatureVector &V) const {
        double res = 0;
        for (size_t i = 0; i < V.size(); i++)
            res += at(V[i]);
        return res;
    }

    template<typename T>
    friend T& operator << (T& out, const FeatureParameter &fp);

    template<typename T>
    friend T& operator >> (T& in, FeatureParameter &fp);
};

template<typename T>
T& operator << (T& out, const FeatureParameter &fp) {
    out << fp.size() << " ";
    for (size_t i = 0; i < fp.size(); i++)
        out << fp[i] << " ";
    out << "\n";
    return out;
}

template<typename T>
T& operator >> (T& in, FeatureParameter &fp) {
    fp.clear();
    size_t n;
    in >> n;
    for (size_t i = 0; i < n; i++) {
        double v;
        in >> v;
        fp.push_back(v);
    }
    return in;
}
