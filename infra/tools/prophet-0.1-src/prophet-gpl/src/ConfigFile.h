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
#include <fstream>
#include <map>

class ConfigFile {
    std::map<std::string, std::string> conf_map;
public:
    ConfigFile(const std::string &filename) {
        std::ifstream fin(filename.c_str(), std::ifstream::in);
        if (fin.is_open()) {
            conf_map.clear();
            while (!fin.eof()) {
                std::string line;
                std::getline(fin, line);
                line = stripLine(line);
                size_t idx = line.find('=');
                if (idx == std::string::npos)
                    break;
                std::string s1 = line.substr(0, idx);
                std::string s2 = line.substr(idx + 1);
                conf_map[s1] = s2;
            }
            fin.close();
        }
        else
            fprintf(stderr, "Unable to open configure file %s\n", filename.c_str());
    }

    ~ConfigFile() {}

    std::string getStr(const std::string &key) {
        std::map<std::string, std::string>::iterator it = conf_map.find(key);
        if (it != conf_map.end())
            return it->second;
        else
            return "";
    }

    bool hasValue(const std::string &key) {
        return conf_map.count(key);
    }
};
