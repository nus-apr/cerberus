all-local: pclang.py tclang.py ld-backup

tclang.py: Makefile.am ../tools/tclang.py
	cp $(srcdir)/../tools/tclang.py ./tclang.py

pclang.py: Makefile.am ../tools/pclang.py
	cp $(srcdir)/../tools/pclang.py ./pclang.py

ld-backup: Makefile.am ../tools/myld.py
	cp $(srcdir)/../tools/myld.py ./ld-backup
