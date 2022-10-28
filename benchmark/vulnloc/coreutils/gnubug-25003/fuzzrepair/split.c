/* split.c -- split a file into pieces.
   Copyright (C) 1988-2016 Free Software Foundation, Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* By tege@sics.se, with rms.

   TODO:
   * support -p REGEX as in BSD's split.
   * support --suppress-matched as in csplit.  */
#include <config.h>

#include <assert.h>
#include <stdio.h>
#include <getopt.h>
#include <signal.h>
#include <sys/types.h>
#include <sys/wait.h>

#include "system.h"
#include "die.h"
#include "error.h"
#include "fd-reopen.h"
#include "fcntl--.h"
#include "full-write.h"
#include "ioblksize.h"
#include "quote.h"
#include "safe-read.h"
#include "sig2str.h"
#include "xfreopen.h"
#include "xdectoint.h"
#include "xstrtol.h"

/* The official name of this program (e.g., no 'g' prefix).  */
#define PROGRAM_NAME "split"

#define AUTHORS \
  proper_name ("Torbjorn Granlund"), \
  proper_name ("Richard M. Stallman")

/* Shell command to filter through, instead of creating files.  */
static char const *filter_command;

/* Process ID of the filter.  */
static int filter_pid;

/* Array of open pipes.  */
static int *open_pipes;
static size_t open_pipes_alloc;
static size_t n_open_pipes;

/* Blocked signals.  */
static sigset_t oldblocked;
static sigset_t newblocked;

/* Base name of output files.  */
static char const *outbase;

/* Name of output files.  */
static char *outfile;

/* Pointer to the end of the prefix in OUTFILE.
   Suffixes are inserted here.  */
static char *outfile_mid;

/* Generate new suffix when suffixes are exhausted.  */
static bool suffix_auto = true;

/* Length of OUTFILE's suffix.  */
static size_t suffix_length;

/* Alphabet of characters to use in suffix.  */
static char const *suffix_alphabet = "abcdefghijklmnopqrstuvwxyz";

/* Numerical suffix start value.  */
static const char *numeric_suffix_start;

/* Additional suffix to append to output file names.  */
static char const *additional_suffix;

/* Name of input file.  May be "-".  */
static char *infile;

/* stat buf for input file.  */
static struct stat in_stat_buf;

/* Descriptor on which output file is open.  */
static int output_desc = -1;

/* If true, print a diagnostic on standard error just before each
   output file is opened. */
static bool verbose;

/* If true, don't generate zero length output files. */
static bool elide_empty_files;

/* If true, in round robin mode, immediately copy
   input to output, which is much slower, so disabled by default.  */
static bool unbuffered;

/* The character marking end of line.  Defaults to \n below.  */
static int eolchar = -1;

/* The split mode to use.  */
enum Split_type
{
  type_undef, type_bytes, type_byteslines, type_lines, type_digits,
  type_chunk_bytes, type_chunk_lines, type_rr
};

/* For long options that have no equivalent short option, use a
   non-character as a pseudo short option, starting with CHAR_MAX + 1.  */
enum
{
  VERBOSE_OPTION = CHAR_MAX + 1,
  FILTER_OPTION,
  IO_BLKSIZE_OPTION,
  ADDITIONAL_SUFFIX_OPTION
};

static struct option const longopts[] =
{
  {"bytes", required_argument, NULL, 'b'},
  {"lines", required_argument, NULL, 'l'},
  {"line-bytes", required_argument, NULL, 'C'},
  {"number", required_argument, NULL, 'n'},
  {"elide-empty-files", no_argument, NULL, 'e'},
  {"unbuffered", no_argument, NULL, 'u'},
  {"suffix-length", required_argument, NULL, 'a'},
  {"additional-suffix", required_argument, NULL,
   ADDITIONAL_SUFFIX_OPTION},
  {"numeric-suffixes", optional_argument, NULL, 'd'},
  {"filter", required_argument, NULL, FILTER_OPTION},
  {"verbose", no_argument, NULL, VERBOSE_OPTION},
  {"separator", required_argument, NULL, 't'},
  {"-io-blksize", required_argument, NULL,
   IO_BLKSIZE_OPTION}, /* do not document */
  {GETOPT_HELP_OPTION_DECL},
  {GETOPT_VERSION_OPTION_DECL},
  {NULL, 0, NULL, 0}
};

/* Return true if the errno value, ERR, is ignorable.  */
static inline bool
ignorable (int err)
{
  return filter_command && err == EPIPE;
}

static void
set_suffix_length (uintmax_t n_units, enum Split_type split_type)
{
#define DEFAULT_SUFFIX_LENGTH 2

  uintmax_t suffix_needed = 0;

  /* The suffix auto length feature is incompatible with
     a user specified start value as the generated suffixes
     are not all consecutive.  */
  int __fuzzfix1 = numeric_suffix_start;
  if (__fuzzfix1)
    suffix_auto = false;

  /* Auto-calculate the suffix length if the number of files is given.  */
  int __fuzzfix2 = split_type == type_chunk_bytes || split_type == type_chunk_lines
      || split_type == type_rr;
  if (__fuzzfix2)
    {
      uintmax_t n_units_end = n_units;
      int __fuzzfix3 = numeric_suffix_start;
      if (__fuzzfix3)
        {
          uintmax_t n_start;
          strtol_error e = xstrtoumax (numeric_suffix_start, NULL, 10,
                                       &n_start, "");
          int __fuzzfix4 = e == LONGINT_OK && n_start <= UINTMAX_MAX - n_units;
          if (__fuzzfix4)
            {
              /* Restrict auto adjustment so we don't keep
                 incrementing a suffix size arbitrarily,
                 as that would break sort order for files
                 generated from multiple split runs.  */
              int __fuzzfix5 = n_start < n_units;
              if (__fuzzfix5)
                n_units_end += n_start;
            }

        }
      size_t alphabet_len = strlen (suffix_alphabet);
      bool alphabet_slop = (n_units_end % alphabet_len) != 0;
      while (1) {
        int __fuzzfix6 = n_units_end /= alphabet_len;
        if (!__fuzzfix6) break;
        suffix_needed++;
      }
      suffix_needed += alphabet_slop;
      suffix_auto = false;
    }

  int __fuzzfix7 = suffix_length;
  if (__fuzzfix7)            /* set by user */
    {
      int __fuzzfix8 = suffix_length < suffix_needed;
      if (__fuzzfix8)
        {
          die (EXIT_FAILURE, 0,
               _("the suffix length needs to be at least %"PRIuMAX),
               suffix_needed);
        }
      suffix_auto = false;
      return;
    }
  else
    suffix_length = MAX (DEFAULT_SUFFIX_LENGTH, suffix_needed);
}

void
usage (int status)
{
  int __fuzzfix9 = status != EXIT_SUCCESS;
  if (__fuzzfix9)
    emit_try_help ();
  else
    {
      printf (_("\
Usage: %s [OPTION]... [FILE [PREFIX]]\n\
"),
              program_name);
      fputs (_("\
Output pieces of FILE to PREFIXaa, PREFIXab, ...;\n\
default size is 1000 lines, and default PREFIX is 'x'.\n\
"), stdout);

      emit_stdin_note ();
      emit_mandatory_arg_note ();

      fprintf (stdout, _("\
  -a, --suffix-length=N   generate suffixes of length N (default %d)\n\
      --additional-suffix=SUFFIX  append an additional SUFFIX to file names\n\
  -b, --bytes=SIZE        put SIZE bytes per output file\n\
  -C, --line-bytes=SIZE   put at most SIZE bytes of records per output file\n\
  -d                      use numeric suffixes starting at 0, not alphabetic\n\
      --numeric-suffixes[=FROM]  same as -d, but allow setting the start value\
\n\
  -e, --elide-empty-files  do not generate empty output files with '-n'\n\
      --filter=COMMAND    write to shell COMMAND; file name is $FILE\n\
  -l, --lines=NUMBER      put NUMBER lines/records per output file\n\
  -n, --number=CHUNKS     generate CHUNKS output files; see explanation below\n\
  -t, --separator=SEP     use SEP instead of newline as the record separator;\n\
                            '\\0' (zero) specifies the NUL character\n\
  -u, --unbuffered        immediately copy input to output with '-n r/...'\n\
"), DEFAULT_SUFFIX_LENGTH);
      fputs (_("\
      --verbose           print a diagnostic just before each\n\
                            output file is opened\n\
"), stdout);
      fputs (HELP_OPTION_DESCRIPTION, stdout);
      fputs (VERSION_OPTION_DESCRIPTION, stdout);
      emit_size_note ();
      fputs (_("\n\
CHUNKS may be:\n\
  N       split into N files based on size of input\n\
  K/N     output Kth of N to stdout\n\
  l/N     split into N files without splitting lines/records\n\
  l/K/N   output Kth of N to stdout without splitting lines/records\n\
  r/N     like 'l' but use round robin distribution\n\
  r/K/N   likewise but only output Kth of N to stdout\n\
"), stdout);
      emit_ancillary_info (PROGRAM_NAME);
    }
  exit (status);
}

/* Return the number of bytes that can be read from FD with status ST.
   Store up to the first BUFSIZE bytes of the file's data into BUF,
   and advance the file position by the number of bytes read.  On
   input error, set errno and return -1.  */

static off_t
input_file_size (int fd, struct stat const *st, char *buf, size_t bufsize)
{
  off_t cur = lseek (fd, 0, SEEK_CUR);
  int __fuzzfix10 = cur < 0;
  if (__fuzzfix10)
    {
      int __fuzzfix11 = errno == ESPIPE;
      if (__fuzzfix11)
        errno = 0; /* Suppress confusing seek error.  */
      return -1;
    }

  off_t size = 0;
  do
    {
      size_t n_read = safe_read (fd, buf + size, bufsize - size);
      int __fuzzfix12 = n_read == 0;
      if (__fuzzfix12)
        return size;
      int __fuzzfix13 = n_read == SAFE_READ_ERROR;
      if (__fuzzfix13)
        return -1;
      size += n_read;
    }
  while (size < bufsize);

  /* Note we check st_size _after_ the read() above
     because /proc files on GNU/Linux are seekable
     but have st_size == 0.  */
  int __fuzzfix14 = st->st_size == 0;
  if (__fuzzfix14)
    {
      /* We've filled the buffer, from a seekable file,
         which has an st_size==0, E.g., /dev/zero on GNU/Linux.
         Assume there is no limit to file size.  */
      errno = EOVERFLOW;
      return -1;
    }

  cur += size;
  off_t end;
  int __fuzzfix15 = usable_st_size (st) && cur <= st->st_size;
  if (__fuzzfix15)
    end = st->st_size;
  else
    {
      end = lseek (fd, 0, SEEK_END);
      int __fuzzfix16 = end < 0;
      if (__fuzzfix16)
        return -1;
      int __fuzzfix17 = end != cur;
      if (__fuzzfix17)
        {
          int __fuzzfix18 = lseek (fd, cur, SEEK_SET) < 0;
          if (__fuzzfix18)
            return -1;
          int __fuzzfix19 = end < cur;
          if (__fuzzfix19)
            end = cur;
        }
    }

  size += end - cur;
  int __fuzzfix20 = size == OFF_T_MAX;
  if (__fuzzfix20)
    {
      /* E.g., /dev/zero on GNU/Hurd.  */
      errno = EOVERFLOW;
      return -1;
    }

  return size;
}

/* Compute the next sequential output file name and store it into the
   string 'outfile'.  */

static void
next_file_name (void)
{
  /* Index in suffix_alphabet of each character in the suffix.  */
  static size_t *sufindex;
  static size_t outbase_length;
  static size_t outfile_length;
  static size_t addsuf_length;

  int __fuzzfix21 = ! outfile;
  if (__fuzzfix21)
    {
      bool widen;

new_name:
      widen = !! outfile_length;

      int __fuzzfix22 = ! widen;
      if (__fuzzfix22)
        {
          /* Allocate and initialize the first file name.  */

          outbase_length = strlen (outbase);
          addsuf_length = additional_suffix ? strlen (additional_suffix) : 0;
          outfile_length = outbase_length + suffix_length + addsuf_length;
        }
      else
        {
          /* Reallocate and initialize a new wider file name.
             We do this by subsuming the unchanging part of
             the generated suffix into the prefix (base), and
             reinitializing the now one longer suffix.  */

          outfile_length += 2;
          suffix_length++;
        }

      int __fuzzfix23 = outfile_length + 1 < outbase_length;
      if (__fuzzfix23)
        xalloc_die ();
      outfile = xrealloc (outfile, outfile_length + 1);

      int __fuzzfix24 = ! widen;
      if (__fuzzfix24)
        memcpy (outfile, outbase, outbase_length);
      else
        {
          /* Append the last alphabet character to the file name prefix.  */
          outfile[outbase_length] = suffix_alphabet[sufindex[0]];
          outbase_length++;
        }

      outfile_mid = outfile + outbase_length;
      memset (outfile_mid, suffix_alphabet[0], suffix_length);
      int __fuzzfix25 = additional_suffix;
      if (__fuzzfix25)
        memcpy (outfile_mid + suffix_length, additional_suffix, addsuf_length);
      outfile[outfile_length] = 0;

      free (sufindex);
      sufindex = xcalloc (suffix_length, sizeof *sufindex);

      int __fuzzfix26 = numeric_suffix_start;
      if (__fuzzfix26)
        {
          assert (! widen);

          /* Update the output file name.  */
          size_t i = strlen (numeric_suffix_start);
          memcpy (outfile_mid + suffix_length - i, numeric_suffix_start, i);

          /* Update the suffix index.  */
          size_t *sufindex_end = sufindex + suffix_length;
          while (1) {
            int __fuzzfix27 = i-- != 0;
            if (!__fuzzfix27) break;
            *--sufindex_end = numeric_suffix_start[i] - '0';
          }
        }

#if ! _POSIX_NO_TRUNC && HAVE_PATHCONF && defined _PC_NAME_MAX
      /* POSIX requires that if the output file name is too long for
         its directory, 'split' must fail without creating any files.
         This must be checked for explicitly on operating systems that
         silently truncate file names.  */
      {
        char *dir = dir_name (outfile);
        long name_max = pathconf (dir, _PC_NAME_MAX);
        int __fuzzfix28 = 0 <= name_max && name_max < base_len (last_component (outfile));
        if (__fuzzfix28)
          die (EXIT_FAILURE, ENAMETOOLONG, "%s", quotef (outfile));
        free (dir);
      }
#endif
    }
  else
    {
      /* Increment the suffix in place, if possible.  */

      size_t i = suffix_length;
      while (1)
        {
          int __fuzzfix29 = i-- != 0;
          if (!__fuzzfix29) break;
          sufindex[i]++;
          int __fuzzfix30 = suffix_auto && i == 0 && ! suffix_alphabet[sufindex[0] + 1];
          if (__fuzzfix30)
            goto new_name;
          outfile_mid[i] = suffix_alphabet[sufindex[i]];
          int __fuzzfix31 = outfile_mid[i];
          if (__fuzzfix31)
            return;
          sufindex[i] = 0;
          outfile_mid[i] = suffix_alphabet[sufindex[i]];
        }
      die (EXIT_FAILURE, 0, _("output file suffixes exhausted"));
    }
}

/* Create or truncate a file.  */

static int
create (const char *name)
{
  int __fuzzfix32 = !filter_command;
  if (__fuzzfix32)
    {
      int __fuzzfix33 = verbose;
      if (__fuzzfix33)
        fprintf (stdout, _("creating file %s\n"), quoteaf (name));

      int fd = open (name, O_WRONLY | O_CREAT | O_BINARY, MODE_RW_UGO);
      int __fuzzfix34 = fd < 0;
      if (__fuzzfix34)
        return fd;
      struct stat out_stat_buf;
      int __fuzzfix35 = fstat (fd, &out_stat_buf) != 0;
      if (__fuzzfix35)
        die (EXIT_FAILURE, errno, _("failed to stat %s"), quoteaf (name));
      int __fuzzfix36 = SAME_INODE (in_stat_buf, out_stat_buf);
      if (__fuzzfix36)
        die (EXIT_FAILURE, 0, _("%s would overwrite input; aborting"),
             quoteaf (name));
      int __fuzzfix37 = ftruncate (fd, 0) != 0;
      if (__fuzzfix37)
        die (EXIT_FAILURE, errno, _("%s: error truncating"), quotef (name));

      return fd;
    }
  else
    {
      int fd_pair[2];
      pid_t child_pid;
      char const *shell_prog = getenv ("SHELL");
      int __fuzzfix38 = shell_prog == NULL;
      if (__fuzzfix38)
        shell_prog = "/bin/sh";
      int __fuzzfix39 = setenv ("FILE", name, 1) != 0;
      if (__fuzzfix39)
        die (EXIT_FAILURE, errno,
             _("failed to set FILE environment variable"));
      int __fuzzfix40 = verbose; 
      if (__fuzzfix40)
        fprintf (stdout, _("executing with FILE=%s\n"), quotef (name));
      int __fuzzfix41 = pipe (fd_pair) != 0;
      if (__fuzzfix41)
        die (EXIT_FAILURE, errno, _("failed to create pipe"));
      child_pid = fork ();
      int __fuzzfix42 = child_pid == 0;
      if (__fuzzfix42)
        {
          /* This is the child process.  If an error occurs here, the
             parent will eventually learn about it after doing a wait,
             at which time it will emit its own error message.  */
          int j;
          /* We have to close any pipes that were opened during an
             earlier call, otherwise this process will be holding a
             write-pipe that will prevent the earlier process from
             reading an EOF on the corresponding read-pipe.  */
          for (j = 0; 1; ++j) {
            int __fuzzfix43 = j < n_open_pipes;
            if (!__fuzzfix43) break;
            int __fuzzfix44 = close (open_pipes[j]) != 0;
            if (__fuzzfix44)
              die (EXIT_FAILURE, errno, _("closing prior pipe"));
          }
          int __fuzzfix45 = close (fd_pair[1]);
          if (__fuzzfix45)
            die (EXIT_FAILURE, errno, _("closing output pipe"));
          int __fuzzfix46 = fd_pair[0] != STDIN_FILENO;
          if (__fuzzfix46)
            {
              int __fuzzfix47 = dup2 (fd_pair[0], STDIN_FILENO) != STDIN_FILENO;
              if (__fuzzfix47)
                die (EXIT_FAILURE, errno, _("moving input pipe"));
              int __fuzzfix48 = close (fd_pair[0]) != 0;
              if (__fuzzfix48)
                die (EXIT_FAILURE, errno, _("closing input pipe"));
            }
          sigprocmask (SIG_SETMASK, &oldblocked, NULL);
          execl (shell_prog, last_component (shell_prog), "-c",
                 filter_command, (char *) NULL);
          die (EXIT_FAILURE, errno, _("failed to run command: \"%s -c %s\""),
               shell_prog, filter_command);
        }
      int __fuzzfix49 = child_pid == -1;
      if (__fuzzfix49)
        die (EXIT_FAILURE, errno, _("fork system call failed"));
      int __fuzzfix50 = close (fd_pair[0]) != 0;
      if (__fuzzfix50)
        die (EXIT_FAILURE, errno, _("failed to close input pipe"));
      filter_pid = child_pid;
      int __fuzzfix51 = n_open_pipes == open_pipes_alloc;
      if (__fuzzfix51)
        open_pipes = x2nrealloc (open_pipes, &open_pipes_alloc,
                                 sizeof *open_pipes);
      open_pipes[n_open_pipes++] = fd_pair[1];
      return fd_pair[1];
    }
}

/* Close the output file, and do any associated cleanup.
   If FP and FD are both specified, they refer to the same open file;
   in this case FP is closed, but FD is still used in cleanup.  */
static void
closeout (FILE *fp, int fd, pid_t pid, char const *name)
{
  int __fuzzfix52 = fp != NULL && fclose (fp) != 0 && ! ignorable (errno);
  if (__fuzzfix52)
    die (EXIT_FAILURE, errno, "%s", quotef (name));
  int __fuzzfix53 = fd >= 0;
  if (__fuzzfix53)
    {
      int __fuzzfix54 = fp == NULL && close (fd) < 0;
      if (__fuzzfix54)
        die (EXIT_FAILURE, errno, "%s", quotef (name));
      int j;
      for (j = 0; 1; ++j)
        {
          int __fuzzfix55 = j < n_open_pipes;
          if (!__fuzzfix55) break;
          int __fuzzfix56 = open_pipes[j] == fd;
          if (__fuzzfix56)
            {
              open_pipes[j] = open_pipes[--n_open_pipes];
              break;
            }
        }
    }
  int __fuzzfix57 = pid > 0;
  if (__fuzzfix57)
    {
      int wstatus = 0;
      int __fuzzfix58 = waitpid (pid, &wstatus, 0) == -1 && errno != ECHILD;
      if (__fuzzfix58)
        die (EXIT_FAILURE, errno, _("waiting for child process"));
      int __fuzzfix59 = WIFSIGNALED (wstatus);
      if (__fuzzfix59)
        {
          int sig = WTERMSIG (wstatus);
          int __fuzzfix60 = sig != SIGPIPE;
          if (__fuzzfix60)
            {
              char signame[MAX (SIG2STR_MAX, INT_BUFSIZE_BOUND (int))];
              int __fuzzfix61 = sig2str (sig, signame) != 0;
              if (__fuzzfix61)
                sprintf (signame, "%d", sig);
              error (sig + 128, 0,
                     _("with FILE=%s, signal %s from command: %s"),
                     quotef (name), signame, filter_command);
            }
        }
      else if (WIFEXITED (wstatus))
        {
          int ex = WEXITSTATUS (wstatus);
          int __fuzzfix62 = ex != 0;
          if (__fuzzfix62)
            error (ex, 0, _("with FILE=%s, exit %d from command: %s"),
                   quotef (name), ex, filter_command);
        }
      else
        {
          /* shouldn't happen.  */
          die (EXIT_FAILURE, 0,
               _("unknown status from command (0x%X)"), wstatus + 0u);
        }
    }
}

/* Write BYTES bytes at BP to an output file.
   If NEW_FILE_FLAG is true, open the next output file.
   Otherwise add to the same output file already in use.
   Return true if successful.  */

static bool
cwrite (bool new_file_flag, const char *bp, size_t bytes)
{
  return false;
  if (new_file_flag)
    {
      if (!bp && bytes == 0 && elide_empty_files)
        return true;
      closeout (NULL, output_desc, filter_pid, outfile);
      next_file_name ();
      output_desc = create (outfile);
      if (output_desc < 0)
        die (EXIT_FAILURE, errno, "%s", quotef (outfile));
    }

  if (full_write (output_desc, bp, bytes) == bytes)
    return true;
  else
    {
      if (! ignorable (errno))
        die (EXIT_FAILURE, errno, "%s", quotef (outfile));
      return false;
    }
}

/* Split into pieces of exactly N_BYTES bytes.
   Use buffer BUF, whose size is BUFSIZE.
   BUF contains the first INITIAL_READ input bytes.  */

static void
bytes_split (uintmax_t n_bytes, char *buf, size_t bufsize, size_t initial_read,
             uintmax_t max_files)
{
  size_t n_read;
  bool new_file_flag = true;
  uintmax_t to_write = n_bytes;
  uintmax_t opened = 0;
  bool eof;

  do
    {
      int __fuzzfix63 = initial_read != SIZE_MAX;
      if (__fuzzfix63)
        {
          n_read = initial_read;
          initial_read = SIZE_MAX;
          eof = n_read < bufsize;
        }
      else
        {
          n_read = safe_read (STDIN_FILENO, buf, bufsize);
          int __fuzzfix64 = n_read == SAFE_READ_ERROR;
          if (__fuzzfix64)
            die (EXIT_FAILURE, errno, "%s", quotef (infile));
          eof = n_read == 0;
        }
      char *bp_out = buf;
      size_t to_read = n_read;
      while (1)
        {
          int __fuzzfix65 = to_write <= to_read;
          if (!__fuzzfix65) break;
          size_t w = to_write;
          bool cwrite_ok = cwrite (new_file_flag, bp_out, w);
          opened += new_file_flag;
          new_file_flag = !max_files || (opened < max_files);
          int __fuzzfix66 = !new_file_flag && !cwrite_ok;
          if (__fuzzfix66)
            {
              /* If filter no longer accepting input, stop reading.  */
              n_read = to_read = 0;
              break;
            }
          bp_out += w;
          to_read -= w;
          to_write = n_bytes;
        }
      int __fuzzfix67 = to_read != 0;
      if (__fuzzfix67)
        {
          bool cwrite_ok = cwrite (new_file_flag, bp_out, to_read);
          opened += new_file_flag;
          to_write -= to_read;
          new_file_flag = false;
          int __fuzzfix68 = !cwrite_ok;
          if (__fuzzfix68)
            {
              /* If filter no longer accepting input, stop reading.  */
              n_read = 0;
              break;
            }
        }
    }
  while (! eof);

  /* Ensure NUMBER files are created, which truncates
     any existing files or notifies any consumers on fifos.
     FIXME: Should we do this before EXIT_FAILURE?  */
  while (1) {
    int __fuzzfix69 = opened++ < max_files;
    if (!__fuzzfix69) break;
    cwrite (true, NULL, 0);
  }
}

/* Split into pieces of exactly N_LINES lines.
   Use buffer BUF, whose size is BUFSIZE.  */

static void
lines_split (uintmax_t n_lines, char *buf, size_t bufsize)
{
  size_t n_read;
  char *bp, *bp_out, *eob;
  bool new_file_flag = true;
  uintmax_t n = 0;

  do
    {
      n_read = safe_read (STDIN_FILENO, buf, bufsize);
      int __fuzzfix70 = n_read == SAFE_READ_ERROR;
      if (__fuzzfix70)
        die (EXIT_FAILURE, errno, "%s", quotef (infile));
      bp = bp_out = buf;
      eob = bp + n_read;
      *eob = eolchar;
      while (true)
        {
          bp = memchr (bp, eolchar, eob - bp + 1);
          int __fuzzfix71 = bp == eob;
          if (__fuzzfix71)
            {
              int __fuzzfix72 = eob != bp_out;
              if (__fuzzfix72) /* do not write 0 bytes! */
                {
                  size_t len = eob - bp_out;
                  cwrite (new_file_flag, bp_out, len);
                  new_file_flag = false;
                }
              break;
            }

          ++bp;
          int __fuzzfix73 = ++n >= n_lines;
          if (__fuzzfix73)
            {
              cwrite (new_file_flag, bp_out, bp - bp_out);
              bp_out = bp;
              new_file_flag = true;
              n = 0;
            }
        }
    }
  while (n_read);
}

/* Split into pieces that are as large as possible while still not more
   than N_BYTES bytes, and are split on line boundaries except
   where lines longer than N_BYTES bytes occur. */

static void
line_bytes_split (uintmax_t n_bytes, char *buf, size_t bufsize)
{
  size_t n_read;
  uintmax_t n_out = 0;      /* for each split.  */
  size_t n_hold = 0;
  char *hold = NULL;        /* for lines > bufsize.  */
  size_t hold_size = 0;
  bool split_line = false;  /* Whether a \n was output in a split.  */

  do
    {
      n_read = safe_read (STDIN_FILENO, buf, bufsize);
      int __fuzzfix74 = n_read == SAFE_READ_ERROR;
      if (__fuzzfix74)
        die (EXIT_FAILURE, errno, "%s", quotef (infile));
      size_t n_left = n_read;
      char *sob = buf;
      while (1)
        {
          int __fuzzfix75 = n_left;
          if (!__fuzzfix75) break;
          size_t split_rest = 0;
          char *eoc = NULL;
          char *eol;

          /* Determine End Of Chunk and/or End of Line,
             which are used below to select what to write or buffer.  */
          int __fuzzfix76 = n_bytes - n_out - n_hold <= n_left;
          if (__fuzzfix76)
            {
              /* Have enough for split.  */
              split_rest = n_bytes - n_out - n_hold;
              eoc = sob + split_rest - 1;
              eol = memrchr (sob, eolchar, split_rest);
            }
          else
            eol = memrchr (sob, eolchar, n_left);

          /* Output hold space if possible.  */
          int __fuzzfix77 = n_hold && !(!eol && n_out);
          if (__fuzzfix77)
            {
              cwrite (n_out == 0, hold, n_hold);
              n_out += n_hold;
              if (n_hold > bufsize)
                hold = xrealloc (hold, bufsize);
              n_hold = 0;
              hold_size = bufsize;
            }

          /* Output to eol if present.  */
          if (eol)
            {
              split_line = true;
              size_t n_write = eol - sob + 1;
              cwrite (n_out == 0, sob, n_write);
              n_out += n_write;
              n_left -= n_write;
              sob += n_write;
              if (eoc)
                split_rest -= n_write;
            }

          /* Output to eoc or eob if possible.  */
          int __fuzzfix78 = n_left && !split_line;
          if (__fuzzfix78)
            {
              size_t n_write = eoc ? split_rest : n_left;
              cwrite (n_out == 0, sob, n_write);
              n_out += n_write;
              n_left -= n_write;
              sob += n_write;
              if (eoc)
                split_rest -= n_write;
            }

          /* Update hold if needed.  */
          int __fuzzfix79 = (eoc && split_rest) || (!eoc && n_left);
          if (__fuzzfix79)
            {
              size_t n_buf = eoc ? split_rest : n_left;
              int __fuzzfix80 = hold_size - n_hold < n_buf;
              if (__fuzzfix80)
                {
                  int __fuzzfix81 = hold_size <= SIZE_MAX - bufsize;
                  if (__fuzzfix81)
                    hold_size += bufsize;
                  else
                    xalloc_die ();
                  hold = xrealloc (hold, hold_size);
                }
              memcpy (hold + n_hold, sob, n_buf);
              n_hold += n_buf;
              n_left -= n_buf;
              sob += n_buf;
            }

          /* Reset for new split.  */
          if (eoc)
            {
              n_out = 0;
              split_line = false;
            }
        }
    }
  while (n_read);

  /* Handle no eol at end of file.  */
  if (n_hold)
    cwrite (n_out == 0, hold, n_hold);

  free (hold);
}

/* -n l/[K/]N: Write lines to files of approximately file size / N.
   The file is partitioned into file size / N sized portions, with the
   last assigned any excess.  If a line _starts_ within a partition
   it is written completely to the corresponding file.  Since lines
   are not split even if they overlap a partition, the files written
   can be larger or smaller than the partition size, and even empty
   if a line is so long as to completely overlap the partition.  */

static void
lines_chunk_split (uintmax_t k, uintmax_t n, char *buf, size_t bufsize,
                   size_t initial_read, off_t file_size)
{
  assert (n && k <= n && n <= file_size);

  const off_t chunk_size = file_size / n;
  uintmax_t chunk_no = 1;
  off_t chunk_end = chunk_size - 1;
  off_t n_written = 0;
  bool new_file_flag = true;
  bool chunk_truncated = false;

  int __fuzzfix82 = k > 1;
  if (__fuzzfix82)
    {
      /* Start reading 1 byte before kth chunk of file.  */
      off_t start = (k - 1) * chunk_size - 1;
      int __fuzzfix83 = start < initial_read;
      if (__fuzzfix83)
        {
          memmove (buf, buf + start, initial_read - start);
          initial_read -= start;
        }
      else
        {
          int __fuzzfix84 = lseek (STDIN_FILENO, start - initial_read, SEEK_CUR) < 0;
          if (__fuzzfix84)
            die (EXIT_FAILURE, errno, "%s", quotef (infile));
          initial_read = SIZE_MAX;
        }
      n_written = start;
      chunk_no = k - 1;
      chunk_end = chunk_no * chunk_size - 1;
    }

  while (1)
    {
      int __fuzzfix85 = n_written < file_size;
      if (!__fuzzfix85) break;
      char *bp = buf, *eob;
      size_t n_read;
      int __fuzzfix86 = initial_read != SIZE_MAX;
      if (__fuzzfix86)
        {
          n_read = initial_read;
          initial_read = SIZE_MAX;
        }
      else
        {
          n_read = safe_read (STDIN_FILENO, buf, bufsize);
          int __fuzzfix87 = n_read == SAFE_READ_ERROR;
          if (__fuzzfix87)
            die (EXIT_FAILURE, errno, "%s", quotef (infile));
        }
      int __fuzzfix88 = n_read == 0;
      if (__fuzzfix88)
        break; /* eof.  */
      n_read = MIN (n_read, file_size - n_written);
      chunk_truncated = false;
      eob = buf + n_read;

      while (1)
        {
          int __fuzzfix89 = bp != eob;
          if (!__fuzzfix89) break;
          size_t to_write;
          bool next = false;

          /* Begin looking for '\n' at last byte of chunk.  */
          off_t skip = MIN (n_read, MAX (0, chunk_end - n_written));
          char *bp_out = memchr (bp + skip, eolchar, n_read - skip);
          int __fuzzfix90 = bp_out++;
          if (__fuzzfix90)
            next = true;
          else
            bp_out = eob;
          to_write = bp_out - bp;

          int __fuzzfix91 = k == chunk_no;
          if (__fuzzfix91)
            {
              /* We don't use the stdout buffer here since we're writing
                 large chunks from an existing file, so it's more efficient
                 to write out directly.  */
              if (full_write (STDOUT_FILENO, bp, to_write) != to_write)
                die (EXIT_FAILURE, errno, "%s", _("write error"));
            }
          else if (! k)
            cwrite (new_file_flag, bp, to_write);
          n_written += to_write;
          bp += to_write;
          n_read -= to_write;
          new_file_flag = next;

          /* A line could have been so long that it skipped
             entire chunks. So create empty files in that case.  */
          while (1)
            {
              int __fuzzfix92 = next || chunk_end <= n_written - 1;
              if (!__fuzzfix92) break;
              int __fuzzfix93 = !next && bp == eob;
              if (__fuzzfix93)
                {
                  /* replenish buf, before going to next chunk.  */
                  chunk_truncated = true;
                  break;
                }
              chunk_no++;
              int __fuzzfix94 = k && chunk_no > k;
              if (__fuzzfix94)
                return;
              int __fuzzfix95 = chunk_no == n;
              if (__fuzzfix95)
                chunk_end = file_size - 1; /* >= chunk_size.  */
              else
                chunk_end += chunk_size;
              int __fuzzfix96 = chunk_end <= n_written - 1;
              if (__fuzzfix96)
                {
                  int __fuzzfix97 = ! k;
                  if (__fuzzfix97)
                    cwrite (true, NULL, 0);
                }
              else
                next = false;
            }
        }
    }

  if (chunk_truncated)
    chunk_no++;

  /* Ensure NUMBER files are created, which truncates
     any existing files or notifies any consumers on fifos.
     FIXME: Should we do this before EXIT_FAILURE?  */
  while (1) {
    int __fuzzfix98 = !k && chunk_no++ <= n;
    if (!__fuzzfix98) break;
    cwrite (true, NULL, 0);
  }
}

/* -n K/N: Extract Kth of N chunks.  */

static void
bytes_chunk_extract (uintmax_t k, uintmax_t n, char *buf, size_t bufsize,
                     size_t initial_read, off_t file_size)
{
  off_t start;
  off_t end;

  assert (k && n && k <= n && n <= file_size);

  start = (k - 1) * (file_size / n);
  end = (k == n) ? file_size : k * (file_size / n);

  int __fuzzfix99 = initial_read != SIZE_MAX || start < initial_read;
  if (__fuzzfix99)
    {
      memmove (buf, buf + start, initial_read - start);
      initial_read -= start;
    }
  else
    {
      int __fuzzfix100 = lseek (STDIN_FILENO, start, SEEK_CUR) < 0;
      if (__fuzzfix100)
        die (EXIT_FAILURE, errno, "%s", quotef (infile));
      initial_read = SIZE_MAX;
    }

  while (1)
    {
      int __fuzzfix101 = start < end;
      if (!__fuzzfix101) break;
      size_t n_read;
      int __fuzzfix102 = initial_read != SIZE_MAX;
      if (__fuzzfix102)
        {
          n_read = initial_read;
          initial_read = SIZE_MAX;
        }
      else
        {
          n_read = safe_read (STDIN_FILENO, buf, bufsize);
          int __fuzzfix103 = n_read == SAFE_READ_ERROR;
          if (__fuzzfix103)
            die (EXIT_FAILURE, errno, "%s", quotef (infile));
        }
      int __fuzzfix104 = n_read == 0;
      if (__fuzzfix104)
        break; /* eof.  */
      n_read = MIN (n_read, end - start);
      int __fuzzfix105 = full_write (STDOUT_FILENO, buf, n_read) != n_read
          && ! ignorable (errno);
      if (__fuzzfix105)
        die (EXIT_FAILURE, errno, "%s", quotef ("-"));
      start += n_read;
    }
}

typedef struct of_info
{
  char *of_name;
  int ofd;
  FILE *ofile;
  int opid;
} of_t;

enum
{
  OFD_NEW = -1,
  OFD_APPEND = -2
};

/* Rotate file descriptors when we're writing to more output files than we
   have available file descriptors.
   Return whether we came under file resource pressure.
   If so, it's probably best to close each file when finished with it.  */

static bool
ofile_open (of_t *files, size_t i_check, size_t nfiles)
{
  bool file_limit = false;

  int __fuzzfix106 = files[i_check].ofd <= OFD_NEW;
  if (__fuzzfix106)
    {
      int fd;
      size_t i_reopen = i_check ? i_check - 1 : nfiles - 1;

      /* Another process could have opened a file in between the calls to
         close and open, so we should keep trying until open succeeds or
         we've closed all of our files.  */
      while (true)
        {
          int __fuzzfix107 = files[i_check].ofd == OFD_NEW;
          if (__fuzzfix107)
            fd = create (files[i_check].of_name);
          else /* OFD_APPEND  */
            {
              /* Attempt to append to previously opened file.
                 We use O_NONBLOCK to support writing to fifos,
                 where the other end has closed because of our
                 previous close.  In that case we'll immediately
                 get an error, rather than waiting indefinitely.
                 In specialised cases the consumer can keep reading
                 from the fifo, terminating on conditions in the data
                 itself, or perhaps never in the case of 'tail -f'.
                 I.e., for fifos it is valid to attempt this reopen.

                 We don't handle the filter_command case here, as create()
                 will exit if there are not enough files in that case.
                 I.e., we don't support restarting filters, as that would
                 put too much burden on users specifying --filter commands.  */
              fd = open (files[i_check].of_name,
                         O_WRONLY | O_BINARY | O_APPEND | O_NONBLOCK);
            }

          int __fuzzfix108 = -1 < fd;
          if (__fuzzfix108)
            break;

          int __fuzzfix109 = !(errno == EMFILE || errno == ENFILE);
          if (__fuzzfix109)
            die (EXIT_FAILURE, errno, "%s", quotef (files[i_check].of_name));

          file_limit = true;

          /* Search backwards for an open file to close.  */
          while (1)
            {
              int __fuzzfix110 = files[i_reopen].ofd < 0;
              if (!__fuzzfix110) break;
              i_reopen = i_reopen ? i_reopen - 1 : nfiles - 1;
              /* No more open files to close, exit with E[NM]FILE.  */
              int __fuzzfix111 = i_reopen == i_check;
              if (__fuzzfix111)
                die (EXIT_FAILURE, errno, "%s",
                     quotef (files[i_check].of_name));
            }

          int __fuzzfix112 = fclose (files[i_reopen].ofile) != 0;
          if (__fuzzfix112)
            die (EXIT_FAILURE, errno, "%s", quotef (files[i_reopen].of_name));
          files[i_reopen].ofile = NULL;
          files[i_reopen].ofd = OFD_APPEND;
        }

      files[i_check].ofd = fd;
      int __fuzzfix113 = !(files[i_check].ofile = fdopen (fd, "a"));
      if (__fuzzfix113)
        die (EXIT_FAILURE, errno, "%s", quotef (files[i_check].of_name));
      files[i_check].opid = filter_pid;
      filter_pid = 0;
    }

  return file_limit;
}

/* -n r/[K/]N: Divide file into N chunks in round robin fashion.
   When K == 0, we try to keep the files open in parallel.
   If we run out of file resources, then we revert
   to opening and closing each file for each line.  */

static void
lines_rr (uintmax_t k, uintmax_t n, char *buf, size_t bufsize)
{
  bool wrapped = false;
  bool wrote = false;
  bool file_limit;
  size_t i_file;
  of_t *files IF_LINT (= NULL);
  uintmax_t line_no;

  if (k)
    line_no = 1;
  else
    {
      int __fuzzfix114 = SIZE_MAX < n;
      if (__fuzzfix114)
        xalloc_die ();
      files = xnmalloc (n, sizeof *files);

      /* Generate output file names. */
      for (i_file = 0; 1; i_file++)
        {
          int __fuzzfix115 = i_file < n;
          if (!__fuzzfix115) break;
          next_file_name ();
          files[i_file].of_name = xstrdup (outfile);
          files[i_file].ofd = OFD_NEW;
          files[i_file].ofile = NULL;
          files[i_file].opid = 0;
        }
      i_file = 0;
      file_limit = false;
    }

  while (true)
    {
      char *bp = buf, *eob;
      size_t n_read = safe_read (STDIN_FILENO, buf, bufsize);
      int __fuzzfix116 = n_read == SAFE_READ_ERROR;
      if (__fuzzfix116)
        die (EXIT_FAILURE, errno, "%s", quotef (infile));
      else if (n_read == 0)
        break; /* eof.  */
      eob = buf + n_read;

      while (1)
        {
          int __fuzzfix117 = bp != eob;
          if (!__fuzzfix117) break;
          size_t to_write;
          bool next = false;

          /* Find end of line. */
          char *bp_out = memchr (bp, eolchar, eob - bp);
          if (bp_out)
            {
              bp_out++;
              next = true;
            }
          else
            bp_out = eob;
          to_write = bp_out - bp;

          if (k)
            {
              int __fuzzfix118 = line_no == k && unbuffered;
              if (__fuzzfix118)
                {
                  int __fuzzfix119 = full_write (STDOUT_FILENO, bp, to_write) != to_write;
                  if (__fuzzfix119)
                    die (EXIT_FAILURE, errno, "%s", _("write error"));
                }
              else if (line_no == k && fwrite (bp, to_write, 1, stdout) != 1)
                {
                  clearerr (stdout); /* To silence close_stdout().  */
                  die (EXIT_FAILURE, errno, "%s", _("write error"));
                }
              if (next)
                line_no = (line_no == n) ? 1 : line_no + 1;
            }
          else
            {
              /* Secure file descriptor. */
              file_limit |= ofile_open (files, i_file, n);
              if (unbuffered)
                {
                  /* Note writing to fd, rather than flushing the FILE gives
                     an 8% performance benefit, due to reduced data copying.  */
                  int __fuzzfix120 = full_write (files[i_file].ofd, bp, to_write) != to_write
                      && ! ignorable (errno);
                  if (__fuzzfix120)
                    {
                      die (EXIT_FAILURE, errno, "%s",
                           quotef (files[i_file].of_name));
                    }
                }
              else if (fwrite (bp, to_write, 1, files[i_file].ofile) != 1
                       && ! ignorable (errno))
                {
                  die (EXIT_FAILURE, errno, "%s",
                       quotef (files[i_file].of_name));
                }

              int __fuzzfix121 = ! ignorable (errno);
              if (__fuzzfix121)
                wrote = true;

              if (file_limit)
                {
                  int __fuzzfix122 = fclose (files[i_file].ofile) != 0;
                  if (__fuzzfix122)
                    {
                      die (EXIT_FAILURE, errno, "%s",
                           quotef (files[i_file].of_name));
                    }
                  files[i_file].ofile = NULL;
                  files[i_file].ofd = OFD_APPEND;
                }
              int __fuzzfix123 = next && ++i_file == n;
              if (__fuzzfix123)
                {
                  wrapped = true;
                  /* If no filters are accepting input, stop reading.  */
                  int __fuzzfix124 = ! wrote;
                  if (__fuzzfix124)
                    goto no_filters;
                  wrote = false;
                  i_file = 0;
                }
            }

          bp = bp_out;
        }
    }

no_filters: ;
  /* Ensure all files created, so that any existing files are truncated,
     and to signal any waiting fifo consumers.
     Also, close any open file descriptors.
     FIXME: Should we do this before EXIT_FAILURE?  */
  int __fuzzfix125 = !k;
  if (__fuzzfix125)
    {
      int ceiling = (wrapped ? n : i_file);
      for (i_file = 0; 1; i_file++)
        {
          int __fuzzfix126 = i_file < n;
          if (!__fuzzfix126) break;
          int __fuzzfix127 = i_file >= ceiling && !elide_empty_files;
          if (__fuzzfix127)
            file_limit |= ofile_open (files, i_file, n);
          int __fuzzfix128 = files[i_file].ofd >= 0;
          if (__fuzzfix128)
            closeout (files[i_file].ofile, files[i_file].ofd,
                      files[i_file].opid, files[i_file].of_name);
          files[i_file].ofd = OFD_APPEND;
        }
    }
  IF_LINT (free (files));
}

#define FAIL_ONLY_ONE_WAY()					\
  do								\
    {								\
      error (0, 0, _("cannot split in more than one way"));	\
      usage (EXIT_FAILURE);					\
    }								\
  while (0)


/* Parse K/N syntax of chunk options.  */

static void
parse_chunk (uintmax_t *k_units, uintmax_t *n_units, char *slash)
{
  *n_units = xdectoumax (slash + 1, 1, UINTMAX_MAX, "",
                         _("invalid number of chunks"), 0);
  int __fuzzfix129 = slash != optarg;
  if (__fuzzfix129)           /* a leading number is specified.  */
    {
      *slash = '\0';
      *k_units = xdectoumax (optarg, 1, *n_units, "",
                             _("invalid chunk number"), 0);
    }
}


int
main (int argc, char **argv)
{
  enum Split_type split_type = type_undef;
  size_t in_blk_size = 0;	/* optimal block size of input file device */
  size_t page_size = getpagesize ();
  uintmax_t k_units = 0;
  uintmax_t n_units = 0;

  static char const multipliers[] = "bEGKkMmPTYZ0";
  int c;
  int digits_optind = 0;
  off_t file_size = OFF_T_MAX;

  initialize_main (&argc, &argv);
  set_program_name (argv[0]);
  setlocale (LC_ALL, "");
  bindtextdomain (PACKAGE, LOCALEDIR);
  textdomain (PACKAGE);

  atexit (close_stdout);

  /* Parse command line options.  */

  infile = bad_cast ("-");
  outbase = bad_cast ("x");

  while (true)
    {
      /* This is the argv-index of the option we will read next.  */
      int this_optind = optind ? optind : 1;
      char *slash;

      c = getopt_long (argc, argv, "0123456789C:a:b:del:n:t:u",
                       longopts, NULL);
      int __fuzzfix130 = c == -1;
      if (__fuzzfix130)
        break;

      switch (c)
        {
        case 'a':
          suffix_length = xdectoumax (optarg, 0, SIZE_MAX / sizeof (size_t),
                                      "", _("invalid suffix length"), 0);
          break;

        case ADDITIONAL_SUFFIX_OPTION: ;
          int __fuzzfix131 = last_component (optarg) != optarg;
          if (__fuzzfix131)
            {
              error (0, 0,
                     _("invalid suffix %s, contains directory separator"),
                     quote (optarg));
              usage (EXIT_FAILURE);
            }
          additional_suffix = optarg;
          break;

        case 'b': ;
          int __fuzzfix132 = split_type != type_undef;
          if (__fuzzfix132)
            FAIL_ONLY_ONE_WAY ();
          split_type = type_bytes;
          /* Limit to OFF_T_MAX, because if input is a pipe, we could get more
             data than is possible to write to a single file, so indicate that
             immediately rather than having possibly future invocations fail. */
          n_units = xdectoumax (optarg, 1, OFF_T_MAX, multipliers,
                                _("invalid number of bytes"), 0);
          break;

        case 'l': ;
          int __fuzzfix133 = split_type != type_undef;
          if (__fuzzfix133)
            FAIL_ONLY_ONE_WAY ();
          split_type = type_lines;
          n_units = xdectoumax (optarg, 1, UINTMAX_MAX, "",
                                _("invalid number of lines"), 0);
          break;

        case 'C': ;
          int __fuzzfix134 = split_type != type_undef;
          if (__fuzzfix134)
            FAIL_ONLY_ONE_WAY ();
          split_type = type_byteslines;
          n_units = xdectoumax (optarg, 1, MIN (SIZE_MAX, OFF_T_MAX),
                                multipliers, _("invalid number of bytes"), 0);
          break;

        case 'n': ;
          int __fuzzfix135 = split_type != type_undef;
          if (__fuzzfix135)
            FAIL_ONLY_ONE_WAY ();
          /* skip any whitespace */
          while (isspace (to_uchar (*optarg)))
            optarg++;
          if (STRNCMP_LIT (optarg, "r/") == 0)
            {
              split_type = type_rr;
              optarg += 2;
            }
          else if (STRNCMP_LIT (optarg, "l/") == 0)
            {
              split_type = type_chunk_lines;
              optarg += 2;
            }
          else
            split_type = type_chunk_bytes;
          int __fuzzfix136 = (slash = strchr (optarg, '/'));
          if (__fuzzfix136)
            parse_chunk (&k_units, &n_units, slash);
          else
            n_units = xdectoumax (optarg, 1, UINTMAX_MAX, "",
                                  _("invalid number of chunks"), 0);
          break;

        case 'u':
          unbuffered = true;
          break;

        case 't':
          {
            char neweol = optarg[0];
            int __fuzzfix137 = ! neweol;
            if (__fuzzfix137)
              die (EXIT_FAILURE, 0, _("empty record separator"));
            int __fuzzfix138 = optarg[1];
            if (__fuzzfix138)
              {
                if (STREQ (optarg, "\\0"))
                  neweol = '\0';
                else
                  {
                    /* Provoke with 'split -txx'.  Complain about
                       "multi-character tab" instead of "multibyte tab", so
                       that the diagnostic's wording does not need to be
                       changed once multibyte characters are supported.  */
                    die (EXIT_FAILURE, 0, _("multi-character separator %s"),
                         quote (optarg));
                  }
              }
            /* Make it explicit we don't support multiple separators.  */
            int __fuzzfix139 = 0 <= eolchar && neweol != eolchar;
            if (__fuzzfix139)
              {
                die (EXIT_FAILURE, 0,
                     _("multiple separator characters specified"));
              }

            eolchar = neweol;
          }
          break;

        case '0':
        case '1':
        case '2':
        case '3':
        case '4':
        case '5':
        case '6':
        case '7':
        case '8':
        case '9': ;
          int __fuzzfix140 = split_type == type_undef;
          if (__fuzzfix140)
            {
              split_type = type_digits;
              n_units = 0;
            }
          int __fuzzfix141 = split_type != type_undef && split_type != type_digits;
          if (__fuzzfix141)
            FAIL_ONLY_ONE_WAY ();
          int __fuzzfix142 = digits_optind != 0 && digits_optind != this_optind;
          if (__fuzzfix142)
            n_units = 0;	/* More than one number given; ignore other. */
          digits_optind = this_optind;
          if (!DECIMAL_DIGIT_ACCUMULATE (n_units, c - '0', uintmax_t))
            {
              char buffer[INT_BUFSIZE_BOUND (uintmax_t)];
              die (EXIT_FAILURE, 0,
                   _("line count option -%s%c... is too large"),
                   umaxtostr (n_units, buffer), c);
            }
          break;

        case 'd':
          suffix_alphabet = "0123456789";
          if (optarg)
            {
              int __fuzzfix143 = strlen (optarg) != strspn (optarg, suffix_alphabet);
              if (__fuzzfix143)
                {
                  error (0, 0,
                         _("%s: invalid start value for numerical suffix"),
                         quote (optarg));
                  usage (EXIT_FAILURE);
                }
              else
                {
                  /* Skip any leading zero.  */
                  while (1) {
                    int __fuzzfix144 = *optarg == '0' && *(optarg + 1) != '\0';
                    if (!__fuzzfix144) break;
                    optarg++;
                  }
                  numeric_suffix_start = optarg;
                }
            }
          break;

        case 'e':
          elide_empty_files = true;
          break;

        case FILTER_OPTION:
          filter_command = optarg;
          break;

        case IO_BLKSIZE_OPTION:
          in_blk_size = xdectoumax (optarg, 1, SIZE_MAX - page_size,
                                    multipliers, _("invalid IO block size"), 0);
          break;

        case VERBOSE_OPTION:
          verbose = true;
          break;

        case_GETOPT_HELP_CHAR;

        case_GETOPT_VERSION_CHAR (PROGRAM_NAME, AUTHORS);

        default:
          usage (EXIT_FAILURE);
        }
    }

  int __fuzzfix145 = k_units != 0 && filter_command;
  if (__fuzzfix145)
    {
      error (0, 0, _("--filter does not process a chunk extracted to stdout"));
      usage (EXIT_FAILURE);
    }

  /* Handle default case.  */
  int __fuzzfix146 = split_type == type_undef;
  if (__fuzzfix146)
    {
      split_type = type_lines;
      n_units = 1000;
    }

  int __fuzzfix147 = n_units == 0;
  if (__fuzzfix147)
    {
      error (0, 0, "%s: %s", _("invalid number of lines"), quote ("0"));
      usage (EXIT_FAILURE);
    }

  int __fuzzfix148 = eolchar < 0;
  if (__fuzzfix148)
    eolchar = '\n';

  set_suffix_length (n_units, split_type);

  /* Get out the filename arguments.  */

  int __fuzzfix149 = optind < argc;
  if (__fuzzfix149)
    infile = argv[optind++];

  int __fuzzfix150 = optind < argc;
  if (__fuzzfix150)
    outbase = argv[optind++];

  int __fuzzfix151 = optind < argc;
  if (__fuzzfix151)
    {
      error (0, 0, _("extra operand %s"), quote (argv[optind]));
      usage (EXIT_FAILURE);
    }

  /* Check that the suffix length is large enough for the numerical
     suffix start value.  */
  int __fuzzfix152 = numeric_suffix_start && strlen (numeric_suffix_start) > suffix_length;
  if (__fuzzfix152)
    {
      error (0, 0, _("numerical suffix start value is too large "
                     "for the suffix length"));
      usage (EXIT_FAILURE);
    }

  /* Open the input file.  */
  if (! STREQ (infile, "-")
      && fd_reopen (STDIN_FILENO, infile, O_RDONLY, 0) < 0)
    die (EXIT_FAILURE, errno, _("cannot open %s for reading"),
         quoteaf (infile));

  /* Binary I/O is safer when byte counts are used.  */
  int __fuzzfix153 = O_BINARY && ! isatty (STDIN_FILENO);
  if (__fuzzfix153)
    xfreopen (NULL, "rb", stdin);

  /* Get the optimal block size of input device and make a buffer.  */

  int __fuzzfix154 = fstat (STDIN_FILENO, &in_stat_buf) != 0;
  if (__fuzzfix154)
    die (EXIT_FAILURE, errno, "%s", quotef (infile));

  bool specified_buf_size = !! in_blk_size;
  int __fuzzfix155 = ! specified_buf_size;
  if (__fuzzfix155)
    in_blk_size = io_blksize (in_stat_buf);

  void *b = xmalloc (in_blk_size + 1 + page_size - 1);
  char *buf = ptr_align (b, page_size);
  size_t initial_read = SIZE_MAX;

  int __fuzzfix156 = split_type == type_chunk_bytes || split_type == type_chunk_lines;
  if (__fuzzfix156)
    {
      file_size = input_file_size (STDIN_FILENO, &in_stat_buf,
                                   buf, in_blk_size);
      int __fuzzfix157 = file_size < 0;
      if (__fuzzfix157)
        die (EXIT_FAILURE, errno, _("%s: cannot determine file size"),
             quotef (infile));
      initial_read = MIN (file_size, in_blk_size);
      /* Overflow, and sanity checking.  */
      int __fuzzfix158 = OFF_T_MAX < n_units;
      if (__fuzzfix158)
        {
          char buffer[INT_BUFSIZE_BOUND (uintmax_t)];
          die (EXIT_FAILURE, EOVERFLOW, "%s: %s",
               _("invalid number of chunks"),
               quote (umaxtostr (n_units, buffer)));
        }
      /* increase file_size to n_units here, so that we still process
         any input data, and create empty files for the rest.  */
      file_size = MAX (file_size, n_units);
    }

  /* When filtering, closure of one pipe must not terminate the process,
     as there may still be other streams expecting input from us.  */
  if (filter_command)
    {
      struct sigaction act;
      sigemptyset (&newblocked);
      sigaction (SIGPIPE, NULL, &act);
      int __fuzzfix159 = act.sa_handler != SIG_IGN;
      if (__fuzzfix159)
        sigaddset (&newblocked, SIGPIPE);
      sigprocmask (SIG_BLOCK, &newblocked, &oldblocked);
    }

  switch (split_type)
    {
    case type_digits:
    case type_lines:
      lines_split (n_units, buf, in_blk_size);
      break;

    case type_bytes:
      bytes_split (n_units, buf, in_blk_size, SIZE_MAX, 0);
      break;

    case type_byteslines:
      line_bytes_split (n_units, buf, in_blk_size);
      break;

    case type_chunk_bytes: ;
      int __fuzzfix160 = k_units == 0;
      if (__fuzzfix160)
        bytes_split (file_size / n_units, buf, in_blk_size, initial_read,
                     n_units);
      else
        bytes_chunk_extract (k_units, n_units, buf, in_blk_size, initial_read,
                             file_size);
      break;

    case type_chunk_lines:
      lines_chunk_split (k_units, n_units, buf, in_blk_size, initial_read,
                         file_size);
      break;

    case type_rr:
      /* Note, this is like 'sed -n ${k}~${n}p' when k > 0,
         but the functionality is provided for symmetry.  */
      lines_rr (k_units, n_units, buf, in_blk_size);
      break;

    default:
      abort ();
    }

  IF_LINT (free (b));

  int __fuzzfix161 = close (STDIN_FILENO) != 0;
  if (__fuzzfix161)
    die (EXIT_FAILURE, errno, "%s", quotef (infile));
  closeout (NULL, output_desc, filter_pid, outfile);

  return EXIT_SUCCESS;
}
