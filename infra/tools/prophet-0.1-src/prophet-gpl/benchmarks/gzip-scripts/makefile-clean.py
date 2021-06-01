#!/usr/bin/env python
from sys import argv

makef = argv[1];
f = open(makef, "r");
lines = f.readlines();
f.close();
f = open(makef, "w");
for line in lines:
    if (line.find("$(srcdir)/Makefile.in:  $(srcdir)/Makefile.am") == 0):
        f.write("$(srcdir)/Makefile.in:  $(am__configure_deps)\n");
    elif (line.find("Makefile: $(srcdir)/Makefile.in") == 0):
        f.write("Makefile: $(top_builddir)/config.status\n");
    else:
        f.write(line);
f.close();
