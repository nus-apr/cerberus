#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_INIT([prophet],[0.1],[fanl@csail.mit.edu, zichaoqi@mit.edu])
AC_CONFIG_AUX_DIR([build-aux])
AC_CONFIG_TESTDIR([tests])
AC_CONFIG_HEADERS([config.h])

AM_INIT_AUTOMAKE([foreign -Wall -Werror -Wno-portability])
m4_ifdef([AM_SILENT_RULES],[AM_SILENT_RULES([yes])])

# Checks for programs.
AM_PROG_CC_C_O
AC_PROG_CXX
AC_PROG_LN_S
AC_PROG_MKDIR_P
AC_PROG_SED

LT_INIT([disable-static pic-only])
AC_PROG_LIBTOOL

AC_DEFINE_UNQUOTED([EXTRA_CLANG_INCLUDE_PATH], [`$srcdir/tools/test_clang_path.py`], 
                   [the extra include path arguments that need to pass to clang when build AST tree])
AC_DEFINE_UNQUOTED([CLANG_WRAP_PATH], ["`readlink -f ./$builddir`/wrap"], 
          [the location of the wrapper for instrument the file])
AC_DEFINE_UNQUOTED([CLANG_CMD], ["`which clang`"],
                   [the clang cmd full path])
AC_DEFINE_UNQUOTED([GCC_CMD], ["`which gcc`"],
                   [the gcc cmd full path])

# Checks for OS.

# Checks for libraries.

# Checks for header files.

# Checks for typedefs, structures, and compiler characteristics.
AC_CHECK_SIZEOF([void *])
AC_CHECK_SIZEOF([int])
AC_CHECK_SIZEOF([long])

# Checks for library functions.

AC_CONFIG_FILES([
	Makefile
	src/Makefile
    benchmarks/Makefile
    benchmarks/php-deps/Makefile
    benchmarks/lighttpd-deps/Makefile
    benchmarks/libtiff-deps/Makefile
    benchmarks/apache-deps/Makefile
    tests/Makefile
    tests/atlocal
    wrap/Makefile
    include/Makefile
])
AC_OUTPUT
