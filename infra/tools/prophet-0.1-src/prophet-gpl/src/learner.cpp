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
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "FeatureVector.h"
#include "FeatureParameter.h"
#include <string>
#include <vector>
#include <fstream>
#include <math.h>
#include <stdlib.h>

llvm::cl::opt<std::string> ConfFile(llvm::cl::Positional, llvm::cl::desc("train_list_file"),
        llvm::cl::value_desc("The list of extracted feature vector files!"), llvm::cl::Required);
llvm::cl::opt<double> LearningRate("alpha", llvm::cl::init(1), llvm::cl::desc("learning_rate"),
        llvm::cl::value_desc("The initial learning rate!"));
llvm::cl::opt<double> Regularity("lambda", llvm::cl::init(1e-3), llvm::cl::desc("regularity_lambda"),
        llvm::cl::value_desc("The regularity factor!"));
llvm::cl::opt<double> RegularityL1("lambdal1", llvm::cl::init(1e-3), llvm::cl::desc("regularity_lambdal1"),
        llvm::cl::value_desc("The regularity l1 factor, default 0."));
llvm::cl::opt<double> ValidationRatio("v", llvm::cl::init(0.15), llvm::cl::desc("validation_ratio"),
        llvm::cl::value_desc("The part of training that we are going to use for validation!"));
llvm::cl::opt<std::string> OutFile("o", llvm::cl::init("para.out"), llvm::cl::desc("output_file"),
        llvm::cl::value_desc("The output file for the parameter!"));
llvm::cl::opt<bool> DumpFeature("dump-feature", llvm::cl::init(false));
llvm::cl::opt<double> HingeMargin("hmargin", llvm::cl::init(0.1), llvm::cl::desc("margin value for hingloss"));
llvm::cl::opt<std::string> LearningAlgo("algo", llvm::cl::init("entropy"), llvm::cl::desc("entropy_or_hingeloss"));

struct TrainingCase {
    std::vector<FeatureVector> cases;
    std::vector<size_t> marked;
};

std::vector<std::string> parseTrainingFList(const std::string &flistf) {
    std::ifstream fin(flistf.c_str(), std::ifstream::in);
    std::string str;
    std::vector<std::string> ret;
    ret.clear();
    while (fin >> str)
        ret.push_back(str);
    return ret;
}

void splitValidation(std::vector<TrainingCase> &T, std::vector<TrainingCase> &V, size_t n) {
    size_t k = T.size() / n;
    std::vector<TrainingCase> tmp = T;
    T.clear();
    for (size_t i = 0; i < tmp.size(); i ++)
        if (( i < n * k) && ( i % k == 0))
            V.push_back(tmp[i]);
        else
            T.push_back(tmp[i]);
}

double get_sign(double x) {
    if (fabs(x) < 1e-6)
        return 0;
    else if (x > 0)
        return 1;
    else
        return -1;
}

FeatureParameter maximumEntropyModel(const std::vector<TrainingCase> &T, const std::vector<TrainingCase> &V, double lambda, double lambdal1, double alpha0) {
    FeatureParameter Theta, bestTheta;
    Theta.resetZero(FeatureVector::MAX_FEATURE);
    bestTheta = Theta;

    double alpha = alpha0;
    double bestResV = -1e20;
    unsigned int round = 0;
    unsigned int last_update = 0;

    while (last_update + 200 > round) {
        round ++;
        double resT = 0;
        std::vector<double> delta;
        delta.resize(Theta.size());
        for (size_t i = 0; i < delta.size(); i++)
            delta[i] = 0;
        for (size_t i = 0; i < T.size(); i++) {
            std::vector<double> a;
            const TrainingCase &c = T[i];
            a.resize(c.cases.size());
            double sumExp = 0;
            for (size_t j = 0; j < c.cases.size(); j++) {
                a[j] = Theta.dotProduct(c.cases[j]);
                sumExp += exp(a[j]);
            }
            for (size_t j = 0; j < c.cases.size(); j++) {
                double p = exp(a[j])/sumExp;
                const FeatureVector &vec = c.cases[j];
                for (size_t k = 0; k < vec.size(); k++) {
                    unsigned int idx = vec[k];
                    delta[idx] -= p;
                    if (vec.getMark()) delta[idx] += ((double)1)/c.marked.size();
                }
                if (vec.getMark())
                    resT += a[j]/c.marked.size();
            }
            resT -= log(sumExp);
        }
        resT /= T.size();
        double adjustedResT = resT;
        for (size_t i = 0; i < delta.size(); i++) {
            delta[i] = delta[i] / T.size() - 2 * lambda * Theta[i] - lambdal1 * get_sign(Theta[i]) ;
            adjustedResT -= lambda * Theta[i] * Theta[i] - lambdal1 * fabs(Theta[i]);
        }
        // update the Theta
        for (size_t i = 0; i < delta.size(); i++)
            Theta[i] += alpha * delta[i];
        // validation set
#if 0
        double resV = 0;
        for (size_t i = 0; i < V.size(); i++) {
            std::vector<double> a;
            TrainingCase &c = V[i];
            a.resize(c.cases.size());
            double sumExp = 0;
            for (size_t j = 0; j < c.cases.size(); j++) {
                a[j] = Theta.dotProduct(c.cases[j]);
                sumExp += exp(a[j]);
            }
            for (size_t j = 0; j < c.marked.size(); j++)
                resV += a[c.marked[j]] / c.marked.size();
            resV -= log(sumExp);
        }
        resV = resV / V.size();
        double adjustedResV = resV;
        for (size_t i = 0; i < Theta.size(); i++)
            adjustedResV -= lambda * Theta[i] * Theta[i];
#else
        double resV = 0;
        for (size_t i = 0; i < V.size(); i++) {
            std::vector<double> a;
            const TrainingCase &c = V[i];
            a.resize(c.cases.size());
            for (size_t j = 0; j < c.cases.size(); j++)
                a[j] = Theta.dotProduct(c.cases[j]);
            size_t max_beat = 0;
            for (size_t k = 0; k < c.marked.size(); k++) {
                size_t beat = 0;
                for (size_t j = 0; j < c.cases.size(); j++)
                    if (a[j] < a[c.marked[k]] || ((a[j] == a[c.marked[k]]) && (j > c.marked[k])))
                        beat++;
                if (max_beat < beat)
                    max_beat = beat;
            }
            resV += ((double)(max_beat) / c.cases.size()) / V.size();
        }
        double adjustedResV = 0;
        for (size_t i = 0; i < T.size(); i++) {
            std::vector<double> a;
            const TrainingCase &c = T[i];
            a.resize(c.cases.size());
            for (size_t j = 0; j < c.cases.size(); j++)
                a[j] = Theta.dotProduct(c.cases[j]);
            size_t max_beat = 0;
            for (size_t k = 0; k < c.marked.size(); k++) {
                size_t beat = 0;
                for (size_t j = 0; j < c.cases.size(); j++)
                    if (a[j] < a[c.marked[k]] || ((a[j] == a[c.marked[k]]) && (j > c.marked[k])))
                        beat++;
                if (max_beat < beat)
                    max_beat = beat;
            }
            adjustedResV += ((double)(max_beat) / c.cases.size()) / T.size();
        }
        adjustedResV = (resV * V.size() + adjustedResV * T.size()) / (V.size() + T.size());
#endif
        llvm::outs() << "Round " << round << ": resT " << resT << " adjResT " << adjustedResT
            << " resV " << resV << " adjResV " << adjustedResV << "\n";
        if (resV > bestResV) {
            bestTheta = Theta;
            bestResV = resV;
            last_update = round;
            llvm::outs() << "Update best!\n";
        }
        else if (alpha > 1) {
            alpha *= 0.1;
            llvm::outs() << "Drop alpha to " << alpha << "\n";
        }
    }
    return bestTheta;
}

FeatureParameter simpleSVMModel(const std::vector<TrainingCase> &T, const std::vector<TrainingCase> &V, double lambda, double lambdal1, double alpha0, double hinge_eps) {
    FeatureParameter Theta, bestTheta;
    Theta.resetZero(FeatureVector::MAX_FEATURE);
    bestTheta = Theta;

    double alpha = alpha0;
    double bestResV = -1e20;
    unsigned int round = 0;
    unsigned int last_update = 0;

    while (last_update + 200 > round) {
        round ++;
        double resT = 0;
        std::vector<double> delta;
        delta.resize(Theta.size());
        for (size_t i = 0; i < delta.size(); i++)
            delta[i] = 0;
        for (size_t i = 0; i < T.size(); i++) {
            std::vector<double> a;
            const TrainingCase &c = T[i];
            a.resize(c.cases.size());
            size_t tot_marked = c.marked.size();
            size_t tot_unmarked = c.cases.size() - tot_marked;
            double diff = 0;
            for (size_t j = 0; j < c.cases.size(); j++) {
                a[j] = Theta.dotProduct(c.cases[j]);
                if (c.cases[j].getMark()) {
                    diff += a[j] / tot_marked;
                }
                else {
                    diff -= a[j] / tot_unmarked;
                }
            }
            if (diff < hinge_eps) {
                resT += diff - hinge_eps;
                for (size_t j = 0; j < c.cases.size(); j++) {
                    const FeatureVector &vec = c.cases[j];
                    if (c.cases[j].getMark()) {
                        for (size_t k = 0; k < vec.size(); k++)
                            delta[vec[k]] += 1.0 / tot_marked;
                    }
                    else {
                        for (size_t k = 0; k < vec.size(); k++)
                            delta[vec[k]] -= 1.0 / tot_unmarked;
                    }
                }
            }
        }
        resT /= T.size();
        double adjustedResT = resT;
        for (size_t i = 0; i < delta.size(); i++) {
            delta[i] = delta[i] / T.size() - 2 * lambda * Theta[i] - lambdal1 * get_sign(Theta[i]) ;
            adjustedResT -= lambda * Theta[i] * Theta[i] - lambdal1 * fabs(Theta[i]);
        }
        // update the Theta
        for (size_t i = 0; i < delta.size(); i++)
            Theta[i] += alpha * delta[i];
        // validation set
        double resV = 0;
        for (size_t i = 0; i < V.size(); i++) {
            std::vector<double> a;
            const TrainingCase &c = V[i];
            a.resize(c.cases.size());
            for (size_t j = 0; j < c.cases.size(); j++)
                a[j] = Theta.dotProduct(c.cases[j]);
            size_t max_beat = 0;
            for (size_t k = 0; k < c.marked.size(); k++) {
                size_t beat = 0;
                for (size_t j = 0; j < c.cases.size(); j++)
                    if (a[j] < a[c.marked[k]] || ((a[j] == a[c.marked[k]]) && (j > c.marked[k])))
                        beat++;
                if (max_beat < beat)
                    max_beat = beat;
            }
            resV += ((double)(max_beat) / c.cases.size()) / V.size();
        }
        double adjustedResV = resV;
        llvm::outs() << "Round " << round << ": resT " << resT << " adjResT " << adjustedResT
            << " resV " << resV << " adjResV " << adjustedResV << "\n";
        if (resV > bestResV) {
            bestTheta = Theta;
            bestResV = resV;
            last_update = round;
            llvm::outs() << "Update best!\n";
        }
        else if (alpha > 0.004) {
            if (last_update + 50 < round) {
                alpha *= 0.9;
                llvm::outs() << "Drop alpha to " << alpha << "\n";
                last_update = round;
            }
        }
    }
    return bestTheta;
}

double vecDis(const FeatureVector &vec1, const FeatureVector &vec2) {
    size_t i = 0;
    size_t j = 0;
    double ret = 0;
    while ((i < vec1.size()) && (j < vec2.size())) {
        if (vec1[i] == vec2[j]) {
            i ++;
            j ++;
        }
        else if (vec1[i] < vec2[j]) {
            i ++;
            ret ++;
        }
        else if (vec1[i] > vec2[j]) {
            j ++;
            ret ++;
        }
    }
    if (i < vec1.size())
        ret += vec1.size() - i;
    if (j < vec2.size())
        ret += vec2.size() - j;
    return sqrt(ret);
}

FeatureParameter hingeLossModel(const std::vector<TrainingCase> &T, const std::vector<TrainingCase> &V, double lambda, double lambdal1, double alpha0, double hinge_eps) {
    FeatureParameter Theta, bestTheta;
    Theta.resetZero(FeatureVector::MAX_FEATURE);
    bestTheta = Theta;

    double alpha = alpha0;
    double bestResV = -1e20;
    unsigned int round = 0;
    unsigned int last_update = 0;

    while (last_update + 200 > round) {
        round ++;
        double resT = 0;
        std::vector<double> delta;
        delta.resize(Theta.size());
        for (size_t i = 0; i < delta.size(); i++)
            delta[i] = 0;
/*        std::set<size_t> helper;
        helper.clear();
        for (size_t i = 0; i < T.size() / 2; i++)
            helper.insert(rand() % T.size());
        for (std::set<size_t>::iterator it = helper.begin(); it != helper.end(); ++it)*/
        for (size_t i = 0; i < T.size(); i++)
        {
            //size_t i = *it;
            std::vector<double> a;
            const TrainingCase &c = T[i];
            a.resize(c.cases.size());
            double bestMarked = -1e20;
            size_t bestMarkedIdx = 0;
            double bestUnmarked = -1e20;
            size_t bestUnmarkedIdx = 0;
            for (size_t j = 0; j < c.cases.size(); j++) {
                a[j] = Theta.dotProduct(c.cases[j]);
                if (c.cases[j].getMark()) {
                    if (bestMarked < a[j]) {
                        bestMarked = a[j];
                        bestMarkedIdx = j;
                    }
                }
            }
            const FeatureVector &bestMarkedVec = c.cases[bestMarkedIdx];
            for (size_t j = 0; j < c.cases.size(); j++) {
                if (!c.cases[j].getMark()) {
                    const FeatureVector &vec = c.cases[j];
                    double dis = vecDis(bestMarkedVec, vec) * hinge_eps;
                    if (a[j] + dis > bestUnmarked) {
                        bestUnmarked = a[j] + dis;
                        bestUnmarkedIdx = j;
                    }
                }
            }
            double hinge = bestMarked - bestUnmarked;
            if (hinge < 0) {
                resT += hinge;
                const FeatureVector &vec = c.cases[bestMarkedIdx];
                for (size_t j = 0; j < vec.size(); j++)
                    delta[vec[j]] += 1;
                const FeatureVector &vec1 = c.cases[bestUnmarkedIdx];
                for (size_t j = 0; j < vec1.size(); j++)
                    delta[vec1[j]] -= 1;
            }
        }
        //resT /= helper.size();
        resT /= T.size();
        double adjustedResT = resT;
        for (size_t i = 0; i < delta.size(); i++) {
            //delta[i] = delta[i] / helper.size() - 2 * lambda * Theta[i] * helper.size() /T.size() - lambdal1 * get_sign(Theta[i]) * helper.size() / T.size();
            delta[i] = delta[i] / T.size() - 2 * lambda * Theta[i] - lambdal1 * get_sign(Theta[i]) ;
            adjustedResT -= lambda * Theta[i] * Theta[i] - lambdal1 * fabs(Theta[i]);
        }
        // update the Theta
        for (size_t i = 0; i < delta.size(); i++)
            Theta[i] += alpha * delta[i];
        // validation set
        double resV = 0;
        for (size_t i = 0; i < V.size(); i++) {
            std::vector<double> a;
            const TrainingCase &c = V[i];
            a.resize(c.cases.size());
            for (size_t j = 0; j < c.cases.size(); j++)
                a[j] = Theta.dotProduct(c.cases[j]);
            size_t max_beat = 0;
            for (size_t k = 0; k < c.marked.size(); k++) {
                size_t beat = 0;
                for (size_t j = 0; j < c.cases.size(); j++)
                    if (a[j] < a[c.marked[k]] || ((a[j] == a[c.marked[k]]) && (j > c.marked[k])))
                        beat++;
                if (max_beat < beat)
                    max_beat = beat;
            }
            resV += ((double)(max_beat) / c.cases.size()) / V.size();
        }
        double adjustedResV = 0;
        for (size_t i = 0; i < T.size(); i++) {
            std::vector<double> a;
            const TrainingCase &c = T[i];
            a.resize(c.cases.size());
            for (size_t j = 0; j < c.cases.size(); j++)
                a[j] = Theta.dotProduct(c.cases[j]);
            size_t max_beat = 0;
            for (size_t k = 0; k < c.marked.size(); k++) {
                size_t beat = 0;
                for (size_t j = 0; j < c.cases.size(); j++)
                    if (a[j] < a[c.marked[k]] || ((a[j] == a[c.marked[k]]) && (j > c.marked[k])))
                        beat++;
                if (max_beat < beat)
                    max_beat = beat;
            }
            adjustedResV += ((double)(max_beat) / c.cases.size()) / T.size();
        }
        adjustedResV = (resV * V.size() + adjustedResV * T.size()) / (V.size() + T.size());
        llvm::outs() << "Round " << round << ": resT " << resT << " adjResT " << adjustedResT
            << " resV " << resV << " adjResV " << adjustedResV << "\n";
        if (resV > bestResV) {
            bestTheta = Theta;
            bestResV = resV;
            last_update = round;
            llvm::outs() << "Update best!\n";
        }
        else if (alpha > 0.004) {
            if (last_update + 100 < round) {
                alpha *= 0.5;
                llvm::outs() << "Drop alpha to " << alpha << "\n";
                last_update = round;
            }
        }
    }
    return bestTheta;
}


int main(int argc, char** argv) {
    llvm::cl::ParseCommandLineOptions(argc, argv);

    unsigned long total_cases = 0;
    unsigned long total_volume = 0;

    std::vector<TrainingCase> T, V;
    std::vector<std::string> trainingFList = parseTrainingFList(ConfFile.getValue());
    T.clear();
    for (size_t i = 0; i < trainingFList.size(); i++) {
        std::ifstream f(trainingFList[i], std::ifstream::in);
        llvm::outs() << "Processing file " + trainingFList[i] + "\n";
        assert(f.is_open() && "Cannot open specified feature file!");
        TrainingCase c;
        c.cases.clear();
        c.marked.clear();
        FeatureVector vec;
        while (f >> vec) {
            c.cases.push_back(vec);
            if (vec.getMark())
                c.marked.push_back(c.cases.size() - 1);
            total_cases ++;
            total_volume += vec.size();
        }
        f.close();
        T.push_back(c);
    }

    llvm::outs() << "Total number of features: " << FeatureVector::MAX_FEATURE << "\n";
    llvm::outs() << "Total number of training set: " << T.size() << "\n";
    llvm::outs() << "Total number of cases: " << total_cases << "\n";
    llvm::outs() << "Total volume: " << total_volume << "\n";

    assert(ValidationRatio.getValue() < 0.5);
    size_t validation_size = (size_t)(T.size() * ValidationRatio.getValue());
    assert( validation_size < T.size());
    splitValidation(T, V, validation_size);
    llvm::outs() << "Total number for training: " << T.size() << "\n";
    llvm::outs() << "Total number for validation: " << V.size() << "\n";

    FeatureParameter Theta;
    if (LearningAlgo.getValue() == "entropy")
        Theta = maximumEntropyModel(T, V, Regularity, RegularityL1, LearningRate.getValue());
    else if (LearningAlgo.getValue() == "simple")
        Theta = simpleSVMModel(T, V, Regularity, RegularityL1, LearningRate.getValue(), HingeMargin.getValue());
    else if (LearningAlgo.getValue() == "ssvm")
        Theta = hingeLossModel(T, V, Regularity, RegularityL1, LearningRate.getValue(), HingeMargin.getValue());
    else {
        llvm::outs() << "Unsupported algorithm! Now only entropy or hingeloss!\n";
        return 1;
    }

    std::ofstream fout(OutFile.getValue().c_str(), std::ofstream::out);
    fout << Theta;
    fout.close();
    if (DumpFeature.getValue())
        Theta.dump(llvm::outs());

    return 0;
}
