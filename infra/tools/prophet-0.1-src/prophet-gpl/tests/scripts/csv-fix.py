#!/usr/bin/env python
import csv
from sys import argv
from os import system
import os
import getopt

finishm = {};
spr = {};

def parseCSV(csvfname):
    slashidx = csvfname.rfind('/');
    lastname = csvfname[slashidx + 1:];
    dash_idx = lastname.find('-');
    dot_idx = lastname.rfind('.');
    scenario = lastname[dash_idx + 1:dot_idx];
    finishm[scenario] = {};
    spr[scenario] = {};
    with open(csvfname, "rU") as csvf:
        csvreader = csv.reader(csvf);
        first_row = True;
        for csvrow in csvreader:
            if first_row:
                first_row = False;
                continue;
            ssize = int(csvrow[2]);
            essize = int(csvrow[5]);
            if essize >= ssize:
                finishm[scenario][csvrow[0]] = csvrow;
            spr[scenario][csvrow[0]] = csvrow;

def transformCSV(csvfname, newfname):
    slashidx = csvfname.rfind('/');
    lastname = csvfname[slashidx + 1:];
    dash_idx = lastname.find('-');
    dot_idx = lastname.rfind('.');
    scenario = lastname[dash_idx + 1:dot_idx];
    fout = open(newfname, 'wb');
    csvwriter = csv.writer(fout);
    with open(csvfname, "rU") as csvf:
        csvreader = csv.reader(csvf);
        first_row = True;
        for csvrow in csvreader:
            if first_row:
                first_row = False;
                csvwriter.writerow(csvrow);
                continue;
            if not csvrow[0] in finishm[scenario]:
                newrow = list(csvrow);
                if (newrow[6] != "") and (newrow[3] != ""):
                    if (int(newrow[6]) > int(newrow[3])):
                        newrow[6] = newrow[3];
            else:
                newrow = list(csvrow);
                newrow[5] = newrow[2];
                newrow[6] = newrow[3];
            ssize = int(newrow[2]);
            essize = int(newrow[5]);
            if (essize >= ssize):
                for i in range(7, 11):
                    if (newrow[i] != "") and (spr[scenario][csvrow[0]][i] != ""):
                        x = int(newrow[i]);
                        y = int(spr[scenario][csvrow[0]][i]);
                        if y > x:
                            newrow[i] = str(y);
            csvwriter.writerow(newrow);

(opts, args) = getopt.getopt(argv[1:], "", []);
in_dir = args[0];
out_dir = args[1];

if not os.path.exists(out_dir):
    system("mkdir " + out_dir);

for root, dirs, files in os.walk(in_dir):
    for csvfname in files:
        if (csvfname[len(csvfname) - 4:] != ".csv"):
            continue;
        if (csvfname[0:3] != "spr"):
            continue;
        parseCSV(root + "/" + csvfname);

for root, dirs, files in os.walk(in_dir):
    for csvfname in files:
        if (csvfname[len(csvfname) - 4:] != ".csv"):
            continue;
        dot_idx = csvfname.rfind(".");
        newfname = out_dir + "/" + csvfname;
        transformCSV(root + "/" + csvfname, newfname);
