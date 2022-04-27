/* $Id$ */

/*
 * Copyright (c) 1988-1997 Sam Leffler
 * Copyright (c) 1991-1997 Silicon Graphics, Inc.
 *
 * Permission to use, copy, modify, distribute, and sell this software and
 * its documentation for any purpose is hereby granted without fee, provided
 * that (i) the above copyright notices and this permission notice appear in
 * all copies of the software and related documentation, and (ii) the names of
 * Sam Leffler and Silicon Graphics may not be used in any advertising or
 * publicity relating to the software without the specific, prior written
 * permission of Sam Leffler and Silicon Graphics.
 *
 * THE SOFTWARE IS PROVIDED "AS-IS" AND WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS, IMPLIED OR OTHERWISE, INCLUDING WITHOUT LIMITATION, ANY
 * WARRANTY OF MERCHANTABILITY OR FITNESS FOR A PARTICULAR PURPOSE.
 *
 * IN NO EVENT SHALL SAM LEFFLER OR SILICON GRAPHICS BE LIABLE FOR
 * ANY SPECIAL, INCIDENTAL, INDIRECT OR CONSEQUENTIAL DAMAGES OF ANY KIND,
 * OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS,
 * WHETHER OR NOT ADVISED OF THE POSSIBILITY OF DAMAGE, AND ON ANY THEORY OF
 * LIABILITY, ARISING OUT OF OR IN CONNECTION WITH THE USE OR PERFORMANCE
 * OF THIS SOFTWARE.
 */

/*
 * TIFF Library.
 *
 * Directory Write Support Routines.
 */
#include "tiffiop.h"

#ifdef HAVE_IEEEFP
#define TIFFCvtNativeToIEEEFloat(tif, n, fp)
#define TIFFCvtNativeToIEEEDouble(tif, n, dp)
#else
extern void TIFFCvtNativeToIEEEFloat(TIFF *tif, uint32 n, float *fp);
extern void TIFFCvtNativeToIEEEDouble(TIFF *tif, uint32 n, double *dp);
#endif

static int TIFFWriteDirectorySec(TIFF *tif, int isimage, int imagedone,
                                 uint64 *pdiroff);

static int TIFFWriteDirectoryTagSampleformatPerSample(TIFF *tif, uint32 *ndir,
                                                      TIFFDirEntry *dir,
                                                      uint16 tag, double value);

static int TIFFWriteDirectoryTagAscii(TIFF *tif, uint32 *ndir,
                                      TIFFDirEntry *dir, uint16 tag,
                                      uint32 count, char *value);
static int TIFFWriteDirectoryTagUndefinedArray(TIFF *tif, uint32 *ndir,
                                               TIFFDirEntry *dir, uint16 tag,
                                               uint32 count, uint8 *value);
static int TIFFWriteDirectoryTagByte(TIFF *tif, uint32 *ndir, TIFFDirEntry *dir,
                                     uint16 tag, uint8 value);
static int TIFFWriteDirectoryTagByteArray(TIFF *tif, uint32 *ndir,
                                          TIFFDirEntry *dir, uint16 tag,
                                          uint32 count, uint8 *value);
static int TIFFWriteDirectoryTagBytePerSample(TIFF *tif, uint32 *ndir,
                                              TIFFDirEntry *dir, uint16 tag,
                                              uint8 value);
static int TIFFWriteDirectoryTagSbyte(TIFF *tif, uint32 *ndir,
                                      TIFFDirEntry *dir, uint16 tag,
                                      int8 value);
static int TIFFWriteDirectoryTagSbyteArray(TIFF *tif, uint32 *ndir,
                                           TIFFDirEntry *dir, uint16 tag,
                                           uint32 count, int8 *value);
static int TIFFWriteDirectoryTagSbytePerSample(TIFF *tif, uint32 *ndir,
                                               TIFFDirEntry *dir, uint16 tag,
                                               int8 value);
static int TIFFWriteDirectoryTagShort(TIFF *tif, uint32 *ndir,
                                      TIFFDirEntry *dir, uint16 tag,
                                      uint16 value);
static int TIFFWriteDirectoryTagShortArray(TIFF *tif, uint32 *ndir,
                                           TIFFDirEntry *dir, uint16 tag,
                                           uint32 count, uint16 *value);
static int TIFFWriteDirectoryTagShortPerSample(TIFF *tif, uint32 *ndir,
                                               TIFFDirEntry *dir, uint16 tag,
                                               uint16 value);
static int TIFFWriteDirectoryTagSshort(TIFF *tif, uint32 *ndir,
                                       TIFFDirEntry *dir, uint16 tag,
                                       int16 value);
static int TIFFWriteDirectoryTagSshortArray(TIFF *tif, uint32 *ndir,
                                            TIFFDirEntry *dir, uint16 tag,
                                            uint32 count, int16 *value);
static int TIFFWriteDirectoryTagSshortPerSample(TIFF *tif, uint32 *ndir,
                                                TIFFDirEntry *dir, uint16 tag,
                                                int16 value);
static int TIFFWriteDirectoryTagLong(TIFF *tif, uint32 *ndir, TIFFDirEntry *dir,
                                     uint16 tag, uint32 value);
static int TIFFWriteDirectoryTagLongArray(TIFF *tif, uint32 *ndir,
                                          TIFFDirEntry *dir, uint16 tag,
                                          uint32 count, uint32 *value);
static int TIFFWriteDirectoryTagLongPerSample(TIFF *tif, uint32 *ndir,
                                              TIFFDirEntry *dir, uint16 tag,
                                              uint32 value);
static int TIFFWriteDirectoryTagSlong(TIFF *tif, uint32 *ndir,
                                      TIFFDirEntry *dir, uint16 tag,
                                      int32 value);
static int TIFFWriteDirectoryTagSlongArray(TIFF *tif, uint32 *ndir,
                                           TIFFDirEntry *dir, uint16 tag,
                                           uint32 count, int32 *value);
static int TIFFWriteDirectoryTagSlongPerSample(TIFF *tif, uint32 *ndir,
                                               TIFFDirEntry *dir, uint16 tag,
                                               int32 value);
static int TIFFWriteDirectoryTagLong8(TIFF *tif, uint32 *ndir,
                                      TIFFDirEntry *dir, uint16 tag,
                                      uint64 value);
static int TIFFWriteDirectoryTagLong8Array(TIFF *tif, uint32 *ndir,
                                           TIFFDirEntry *dir, uint16 tag,
                                           uint32 count, uint64 *value);
static int TIFFWriteDirectoryTagSlong8(TIFF *tif, uint32 *ndir,
                                       TIFFDirEntry *dir, uint16 tag,
                                       int64 value);
static int TIFFWriteDirectoryTagSlong8Array(TIFF *tif, uint32 *ndir,
                                            TIFFDirEntry *dir, uint16 tag,
                                            uint32 count, int64 *value);
static int TIFFWriteDirectoryTagRational(TIFF *tif, uint32 *ndir,
                                         TIFFDirEntry *dir, uint16 tag,
                                         double value);
static int TIFFWriteDirectoryTagRationalArray(TIFF *tif, uint32 *ndir,
                                              TIFFDirEntry *dir, uint16 tag,
                                              uint32 count, float *value);
static int TIFFWriteDirectoryTagSrationalArray(TIFF *tif, uint32 *ndir,
                                               TIFFDirEntry *dir, uint16 tag,
                                               uint32 count, float *value);
static int TIFFWriteDirectoryTagFloat(TIFF *tif, uint32 *ndir,
                                      TIFFDirEntry *dir, uint16 tag,
                                      float value);
static int TIFFWriteDirectoryTagFloatArray(TIFF *tif, uint32 *ndir,
                                           TIFFDirEntry *dir, uint16 tag,
                                           uint32 count, float *value);
static int TIFFWriteDirectoryTagFloatPerSample(TIFF *tif, uint32 *ndir,
                                               TIFFDirEntry *dir, uint16 tag,
                                               float value);
static int TIFFWriteDirectoryTagDouble(TIFF *tif, uint32 *ndir,
                                       TIFFDirEntry *dir, uint16 tag,
                                       double value);
static int TIFFWriteDirectoryTagDoubleArray(TIFF *tif, uint32 *ndir,
                                            TIFFDirEntry *dir, uint16 tag,
                                            uint32 count, double *value);
static int TIFFWriteDirectoryTagDoublePerSample(TIFF *tif, uint32 *ndir,
                                                TIFFDirEntry *dir, uint16 tag,
                                                double value);
static int TIFFWriteDirectoryTagIfdArray(TIFF *tif, uint32 *ndir,
                                         TIFFDirEntry *dir, uint16 tag,
                                         uint32 count, uint32 *value);
static int TIFFWriteDirectoryTagIfd8Array(TIFF *tif, uint32 *ndir,
                                          TIFFDirEntry *dir, uint16 tag,
                                          uint32 count, uint64 *value);
static int TIFFWriteDirectoryTagShortLong(TIFF *tif, uint32 *ndir,
                                          TIFFDirEntry *dir, uint16 tag,
                                          uint32 value);
static int TIFFWriteDirectoryTagLongLong8Array(TIFF *tif, uint32 *ndir,
                                               TIFFDirEntry *dir, uint16 tag,
                                               uint32 count, uint64 *value);
static int TIFFWriteDirectoryTagShortLongLong8Array(TIFF *tif, uint32 *ndir,
                                                    TIFFDirEntry *dir,
                                                    uint16 tag, uint32 count,
                                                    uint64 *value);
static int TIFFWriteDirectoryTagColormap(TIFF *tif, uint32 *ndir,
                                         TIFFDirEntry *dir);
static int TIFFWriteDirectoryTagTransferfunction(TIFF *tif, uint32 *ndir,
                                                 TIFFDirEntry *dir);
static int TIFFWriteDirectoryTagSubifd(TIFF *tif, uint32 *ndir,
                                       TIFFDirEntry *dir);

static int TIFFWriteDirectoryTagCheckedAscii(TIFF *tif, uint32 *ndir,
                                             TIFFDirEntry *dir, uint16 tag,
                                             uint32 count, char *value);
static int TIFFWriteDirectoryTagCheckedUndefinedArray(TIFF *tif, uint32 *ndir,
                                                      TIFFDirEntry *dir,
                                                      uint16 tag, uint32 count,
                                                      uint8 *value);
static int TIFFWriteDirectoryTagCheckedByte(TIFF *tif, uint32 *ndir,
                                            TIFFDirEntry *dir, uint16 tag,
                                            uint8 value);
static int TIFFWriteDirectoryTagCheckedByteArray(TIFF *tif, uint32 *ndir,
                                                 TIFFDirEntry *dir, uint16 tag,
                                                 uint32 count, uint8 *value);
static int TIFFWriteDirectoryTagCheckedSbyte(TIFF *tif, uint32 *ndir,
                                             TIFFDirEntry *dir, uint16 tag,
                                             int8 value);
static int TIFFWriteDirectoryTagCheckedSbyteArray(TIFF *tif, uint32 *ndir,
                                                  TIFFDirEntry *dir, uint16 tag,
                                                  uint32 count, int8 *value);
static int TIFFWriteDirectoryTagCheckedShort(TIFF *tif, uint32 *ndir,
                                             TIFFDirEntry *dir, uint16 tag,
                                             uint16 value);
static int TIFFWriteDirectoryTagCheckedShortArray(TIFF *tif, uint32 *ndir,
                                                  TIFFDirEntry *dir, uint16 tag,
                                                  uint32 count, uint16 *value);
static int TIFFWriteDirectoryTagCheckedSshort(TIFF *tif, uint32 *ndir,
                                              TIFFDirEntry *dir, uint16 tag,
                                              int16 value);
static int TIFFWriteDirectoryTagCheckedSshortArray(TIFF *tif, uint32 *ndir,
                                                   TIFFDirEntry *dir,
                                                   uint16 tag, uint32 count,
                                                   int16 *value);
static int TIFFWriteDirectoryTagCheckedLong(TIFF *tif, uint32 *ndir,
                                            TIFFDirEntry *dir, uint16 tag,
                                            uint32 value);
static int TIFFWriteDirectoryTagCheckedLongArray(TIFF *tif, uint32 *ndir,
                                                 TIFFDirEntry *dir, uint16 tag,
                                                 uint32 count, uint32 *value);
static int TIFFWriteDirectoryTagCheckedSlong(TIFF *tif, uint32 *ndir,
                                             TIFFDirEntry *dir, uint16 tag,
                                             int32 value);
static int TIFFWriteDirectoryTagCheckedSlongArray(TIFF *tif, uint32 *ndir,
                                                  TIFFDirEntry *dir, uint16 tag,
                                                  uint32 count, int32 *value);
static int TIFFWriteDirectoryTagCheckedLong8(TIFF *tif, uint32 *ndir,
                                             TIFFDirEntry *dir, uint16 tag,
                                             uint64 value);
static int TIFFWriteDirectoryTagCheckedLong8Array(TIFF *tif, uint32 *ndir,
                                                  TIFFDirEntry *dir, uint16 tag,
                                                  uint32 count, uint64 *value);
static int TIFFWriteDirectoryTagCheckedSlong8(TIFF *tif, uint32 *ndir,
                                              TIFFDirEntry *dir, uint16 tag,
                                              int64 value);
static int TIFFWriteDirectoryTagCheckedSlong8Array(TIFF *tif, uint32 *ndir,
                                                   TIFFDirEntry *dir,
                                                   uint16 tag, uint32 count,
                                                   int64 *value);
static int TIFFWriteDirectoryTagCheckedRational(TIFF *tif, uint32 *ndir,
                                                TIFFDirEntry *dir, uint16 tag,
                                                double value);
static int TIFFWriteDirectoryTagCheckedRationalArray(TIFF *tif, uint32 *ndir,
                                                     TIFFDirEntry *dir,
                                                     uint16 tag, uint32 count,
                                                     float *value);
static int TIFFWriteDirectoryTagCheckedSrationalArray(TIFF *tif, uint32 *ndir,
                                                      TIFFDirEntry *dir,
                                                      uint16 tag, uint32 count,
                                                      float *value);
static int TIFFWriteDirectoryTagCheckedFloat(TIFF *tif, uint32 *ndir,
                                             TIFFDirEntry *dir, uint16 tag,
                                             float value);
static int TIFFWriteDirectoryTagCheckedFloatArray(TIFF *tif, uint32 *ndir,
                                                  TIFFDirEntry *dir, uint16 tag,
                                                  uint32 count, float *value);
static int TIFFWriteDirectoryTagCheckedDouble(TIFF *tif, uint32 *ndir,
                                              TIFFDirEntry *dir, uint16 tag,
                                              double value);
static int TIFFWriteDirectoryTagCheckedDoubleArray(TIFF *tif, uint32 *ndir,
                                                   TIFFDirEntry *dir,
                                                   uint16 tag, uint32 count,
                                                   double *value);
static int TIFFWriteDirectoryTagCheckedIfdArray(TIFF *tif, uint32 *ndir,
                                                TIFFDirEntry *dir, uint16 tag,
                                                uint32 count, uint32 *value);
static int TIFFWriteDirectoryTagCheckedIfd8Array(TIFF *tif, uint32 *ndir,
                                                 TIFFDirEntry *dir, uint16 tag,
                                                 uint32 count, uint64 *value);

static int TIFFWriteDirectoryTagData(TIFF *tif, uint32 *ndir, TIFFDirEntry *dir,
                                     uint16 tag, uint16 datatype, uint32 count,
                                     uint32 datalength, void *data);

static int TIFFLinkDirectory(TIFF *);

/*
 * Write the contents of the current directory
 * to the specified file.  This routine doesn't
 * handle overwriting a directory with auxiliary
 * storage that's been changed.
 */
int TIFFWriteDirectory(TIFF *tif) {
  return TIFFWriteDirectorySec(tif, TRUE, TRUE, NULL);
}

/*
 * Similar to TIFFWriteDirectory(), writes the directory out
 * but leaves all data structures in memory so that it can be
 * written again.  This will make a partially written TIFF file
 * readable before it is successfully completed/closed.
 */
int TIFFCheckpointDirectory(TIFF *tif) {
  int rc;
  /* Setup the strips arrays, if they haven't already been. */
 /* jump:284 */  if (tif->tif_dir.td_stripoffset == NULL) {
    (void)TIFFSetupStrips(tif);
  }
  rc = TIFFWriteDirectorySec(tif, TRUE, FALSE, NULL);
  (void)TIFFSetWriteOffset(tif, TIFFSeekFile(tif, 0, SEEK_END));
  return rc;
}

int TIFFWriteCustomDirectory(TIFF *tif, uint64 *pdiroff) {
  return TIFFWriteDirectorySec(tif, FALSE, FALSE, pdiroff);
}

/*
 * Similar to TIFFWriteDirectory(), but if the directory has already
 * been written once, it is relocated to the end of the file, in case it
 * has changed in size.  Note that this will result in the loss of the
 * previously used directory space.
 */
int TIFFRewriteDirectory(TIFF *tif) {
  static const char module[] = "TIFFRewriteDirectory";

  /* We don't need to do anything special if it hasn't been written. */
 /* jump:306 */  if (tif->tif_diroff == 0) {
    return TIFFWriteDirectory(tif);
  }

  /*
   * Find and zero the pointer to this directory, so that TIFFLinkDirectory
   * will cause it to be added after this directories current pre-link.
   */

 /* jump:363 */  if (!(tif->tif_flags & TIFF_BIGTIFF)) {
 /* jump:324 */    if (tif->tif_header.classic.tiff_diroff == tif->tif_diroff) {
      tif->tif_header.classic.tiff_diroff = 0;
      tif->tif_diroff = 0;

      TIFFSeekFile(tif, 4, SEEK_SET);
 /* jump:323 */      if (!WriteOK(tif, &(tif->tif_header.classic.tiff_diroff), 4)) {
        TIFFErrorExt(tif->tif_clientdata, tif->tif_name,
                     "Error updating TIFF header");
        return (0);
      }
    } else {
      uint32 nextdir;
      nextdir = tif->tif_header.classic.tiff_diroff;
 /* jump:361 */      while (1) {
        uint16 dircount;
        uint32 nextnextdir;

 /* jump:335 */        if (!SeekOK(tif, nextdir) || !ReadOK(tif, &dircount, 2)) {
          TIFFErrorExt(tif->tif_clientdata, module,
                       "Error fetching directory count");
          return (0);
        }
 /* jump:338 */        if (tif->tif_flags & TIFF_SWAB) {
          TIFFSwabShort(&dircount);
        }
        (void)TIFFSeekFile(tif, nextdir + 2 + dircount * 12, SEEK_SET);
 /* jump:344 */        if (!ReadOK(tif, &nextnextdir, 4)) {
          TIFFErrorExt(tif->tif_clientdata, module,
                       "Error fetching directory link");
          return (0);
        }
 /* jump:347 */        if (tif->tif_flags & TIFF_SWAB) {
          TIFFSwabLong(&nextnextdir);
        }
 /* jump:359 */        if (nextnextdir == tif->tif_diroff) {
          uint32 m;
          m = 0;
          (void)TIFFSeekFile(tif, nextdir + 2 + dircount * 12, SEEK_SET);
 /* jump:356 */          if (!WriteOK(tif, &m, 4)) {
            TIFFErrorExt(tif->tif_clientdata, module,
                         "Error writing directory link");
            return (0);
          }
          tif->tif_diroff = 0;
          break;
        }
        nextdir = nextnextdir;
      }
    }
  } else {
 /* jump:374 */    if (tif->tif_header.big.tiff_diroff == tif->tif_diroff) {
      tif->tif_header.big.tiff_diroff = 0;
      tif->tif_diroff = 0;

      TIFFSeekFile(tif, 8, SEEK_SET);
 /* jump:373 */      if (!WriteOK(tif, &(tif->tif_header.big.tiff_diroff), 8)) {
        TIFFErrorExt(tif->tif_clientdata, tif->tif_name,
                     "Error updating TIFF header");
        return (0);
      }
    } else {
      uint64 nextdir;
      nextdir = tif->tif_header.big.tiff_diroff;
 /* jump:418 */      while (1) {
        uint64 dircount64;
        uint16 dircount;
        uint64 nextnextdir;

 /* jump:386 */        if (!SeekOK(tif, nextdir) || !ReadOK(tif, &dircount64, 8)) {
          TIFFErrorExt(tif->tif_clientdata, module,
                       "Error fetching directory count");
          return (0);
        }
 /* jump:389 */        if (tif->tif_flags & TIFF_SWAB) {
          TIFFSwabLong8(&dircount64);
        }
 /* jump:394 */        if (dircount64 > 0xFFFF) {
          TIFFErrorExt(tif->tif_clientdata, module,
                       "Sanity check on tag count failed, likely corrupt TIFF");
          return (0);
        }
        dircount = (uint16)dircount64;
        (void)TIFFSeekFile(tif, nextdir + 8 + dircount * 20, SEEK_SET);
 /* jump:401 */        if (!ReadOK(tif, &nextnextdir, 8)) {
          TIFFErrorExt(tif->tif_clientdata, module,
                       "Error fetching directory link");
          return (0);
        }
 /* jump:404 */        if (tif->tif_flags & TIFF_SWAB) {
          TIFFSwabLong8(&nextnextdir);
        }
 /* jump:416 */        if (nextnextdir == tif->tif_diroff) {
          uint64 m;
          m = 0;
          (void)TIFFSeekFile(tif, nextdir + 8 + dircount * 20, SEEK_SET);
 /* jump:413 */          if (!WriteOK(tif, &m, 8)) {
            TIFFErrorExt(tif->tif_clientdata, module,
                         "Error writing directory link");
            return (0);
          }
          tif->tif_diroff = 0;
          break;
        }
        nextdir = nextnextdir;
      }
    }
  }

  /*
   * Now use TIFFWriteDirectory() normally.
   */

  return TIFFWriteDirectory(tif);
}

static int TIFFWriteDirectorySec(TIFF *tif, int isimage, int imagedone,
                                 uint64 *pdiroff) {
  static const char module[] = "TIFFWriteDirectorySec";
  uint32 ndir;
  TIFFDirEntry *dir;
  uint32 dirsize;
  void *dirmem;
  uint32 m;
 /* jump:439 */  if (tif->tif_mode == O_RDONLY) {
    return (1);
  }
  /*
   * Clear write state so that subsequent images with
   * different characteristics get the right buffers
   * setup for them.
   */
 /* jump:477 */  if (imagedone) {
    tmsize_t orig_rawcc = tif->tif_rawcc;

 /* jump:455 */    if (tif->tif_flags & TIFF_POSTENCODE) {
      tif->tif_flags &= ~TIFF_POSTENCODE;
 /* jump:454 */      if (!(*tif->tif_postencode)(tif)) {
        TIFFErrorExt(tif->tif_clientdata, module,
                     "Error post-encoding before directory write");
        return (0);
      }
    }
    (*tif->tif_close)(tif); /* shutdown encoder */
    /*
     * Flush any data that might have been written
     * by the compression close+cleanup routines.  But
     * be careful not to write stuff if we didn't add data
     * in the previous steps as the "rawcc" data may well be
     * a previously read tile/strip in mixed read/write mode.
     */
 /* jump:469 */    if (tif->tif_rawcc > 0 && tif->tif_rawcc != orig_rawcc &&
        (tif->tif_flags & TIFF_BEENWRITING) != 0 && !TIFFFlushData1(tif)) {
      TIFFErrorExt(tif->tif_clientdata, module,
                   "Error flushing data before directory write");
      return (0);
    }
 /* jump:475 */    if ((tif->tif_flags & TIFF_MYBUFFER) && tif->tif_rawdata) {
      _TIFFfree(tif->tif_rawdata);
      tif->tif_rawdata = NULL;
      tif->tif_rawcc = 0;
      tif->tif_rawdatasize = 0;
    }
    tif->tif_flags &= ~(TIFF_BEENWRITING | TIFF_BUFFERSETUP);
  }
  dir = NULL;
  dirmem = NULL;
  dirsize = 0;
 /* jump:985 */  while (1) {
    ndir = 0;
 /* jump:794 */    if (isimage) {
 /* jump:494 */      if (TIFFFieldSet(tif, FIELD_IMAGEDIMENSIONS)) {
 /* jump:488 */        if (!TIFFWriteDirectoryTagShortLong(tif, &ndir, dir, TIFFTAG_IMAGEWIDTH,
                                            tif->tif_dir.td_imagewidth)) {
          goto bad;
        }
 /* jump:493 */        if (!TIFFWriteDirectoryTagShortLong(tif, &ndir, dir,
                                            TIFFTAG_IMAGELENGTH,
                                            tif->tif_dir.td_imagelength)) {
          goto bad;
        }
      }
 /* jump:504 */      if (TIFFFieldSet(tif, FIELD_TILEDIMENSIONS)) {
 /* jump:499 */        if (!TIFFWriteDirectoryTagShortLong(tif, &ndir, dir, TIFFTAG_TILEWIDTH,
                                            tif->tif_dir.td_tilewidth)) {
          goto bad;
        }
 /* jump:503 */        if (!TIFFWriteDirectoryTagShortLong(tif, &ndir, dir, TIFFTAG_TILELENGTH,
                                            tif->tif_dir.td_tilelength)) {
          goto bad;
        }
      }
 /* jump:514 */      if (TIFFFieldSet(tif, FIELD_RESOLUTION)) {
 /* jump:509 */        if (!TIFFWriteDirectoryTagRational(tif, &ndir, dir, TIFFTAG_XRESOLUTION,
                                           tif->tif_dir.td_xresolution)) {
          goto bad;
        }
 /* jump:513 */        if (!TIFFWriteDirectoryTagRational(tif, &ndir, dir, TIFFTAG_YRESOLUTION,
                                           tif->tif_dir.td_yresolution)) {
          goto bad;
        }
      }
 /* jump:524 */      if (TIFFFieldSet(tif, FIELD_POSITION)) {
 /* jump:519 */        if (!TIFFWriteDirectoryTagRational(tif, &ndir, dir, TIFFTAG_XPOSITION,
                                           tif->tif_dir.td_xposition)) {
          goto bad;
        }
 /* jump:523 */        if (!TIFFWriteDirectoryTagRational(tif, &ndir, dir, TIFFTAG_YPOSITION,
                                           tif->tif_dir.td_yposition)) {
          goto bad;
        }
      }
 /* jump:530 */      if (TIFFFieldSet(tif, FIELD_SUBFILETYPE)) {
 /* jump:529 */        if (!TIFFWriteDirectoryTagLong(tif, &ndir, dir, TIFFTAG_SUBFILETYPE,
                                       tif->tif_dir.td_subfiletype)) {
          goto bad;
        }
      }
 /* jump:537 */      if (TIFFFieldSet(tif, FIELD_BITSPERSAMPLE)) {
 /* jump:536 */        if (!TIFFWriteDirectoryTagShortPerSample(
                tif, &ndir, dir, TIFFTAG_BITSPERSAMPLE,
                tif->tif_dir.td_bitspersample)) {
          goto bad;
        }
      }
 /* jump:543 */      if (TIFFFieldSet(tif, FIELD_COMPRESSION)) {
 /* jump:542 */        if (!TIFFWriteDirectoryTagShort(tif, &ndir, dir, TIFFTAG_COMPRESSION,
                                        tif->tif_dir.td_compression)) {
          goto bad;
        }
      }
 /* jump:549 */      if (TIFFFieldSet(tif, FIELD_PHOTOMETRIC)) {
 /* jump:548 */        if (!TIFFWriteDirectoryTagShort(tif, &ndir, dir, TIFFTAG_PHOTOMETRIC,
                                        tif->tif_dir.td_photometric)) {
          goto bad;
        }
      }
 /* jump:555 */      if (TIFFFieldSet(tif, FIELD_THRESHHOLDING)) {
 /* jump:554 */        if (!TIFFWriteDirectoryTagShort(tif, &ndir, dir, TIFFTAG_THRESHHOLDING,
                                        tif->tif_dir.td_threshholding)) {
          goto bad;
        }
      }
 /* jump:561 */      if (TIFFFieldSet(tif, FIELD_FILLORDER)) {
 /* jump:560 */        if (!TIFFWriteDirectoryTagShort(tif, &ndir, dir, TIFFTAG_FILLORDER,
                                        tif->tif_dir.td_fillorder)) {
          goto bad;
        }
      }
 /* jump:567 */      if (TIFFFieldSet(tif, FIELD_ORIENTATION)) {
 /* jump:566 */        if (!TIFFWriteDirectoryTagShort(tif, &ndir, dir, TIFFTAG_ORIENTATION,
                                        tif->tif_dir.td_orientation)) {
          goto bad;
        }
      }
 /* jump:574 */      if (TIFFFieldSet(tif, FIELD_SAMPLESPERPIXEL)) {
 /* jump:573 */        if (!TIFFWriteDirectoryTagShort(tif, &ndir, dir,
                                        TIFFTAG_SAMPLESPERPIXEL,
                                        tif->tif_dir.td_samplesperpixel)) {
          goto bad;
        }
      }
 /* jump:581 */      if (TIFFFieldSet(tif, FIELD_ROWSPERSTRIP)) {
 /* jump:580 */        if (!TIFFWriteDirectoryTagShortLong(tif, &ndir, dir,
                                            TIFFTAG_ROWSPERSTRIP,
                                            tif->tif_dir.td_rowsperstrip)) {
          goto bad;
        }
      }
 /* jump:588 */      if (TIFFFieldSet(tif, FIELD_MINSAMPLEVALUE)) {
 /* jump:587 */        if (!TIFFWriteDirectoryTagShortPerSample(
                tif, &ndir, dir, TIFFTAG_MINSAMPLEVALUE,
                tif->tif_dir.td_minsamplevalue)) {
          goto bad;
        }
      }
 /* jump:595 */      if (TIFFFieldSet(tif, FIELD_MAXSAMPLEVALUE)) {
 /* jump:594 */        if (!TIFFWriteDirectoryTagShortPerSample(
                tif, &ndir, dir, TIFFTAG_MAXSAMPLEVALUE,
                tif->tif_dir.td_maxsamplevalue)) {
          goto bad;
        }
      }
 /* jump:601 */      if (TIFFFieldSet(tif, FIELD_PLANARCONFIG)) {
 /* jump:600 */        if (!TIFFWriteDirectoryTagShort(tif, &ndir, dir, TIFFTAG_PLANARCONFIG,
                                        tif->tif_dir.td_planarconfig)) {
          goto bad;
        }
      }
 /* jump:607 */      if (TIFFFieldSet(tif, FIELD_RESOLUTIONUNIT)) {
 /* jump:606 */        if (!TIFFWriteDirectoryTagShort(tif, &ndir, dir, TIFFTAG_RESOLUTIONUNIT,
                                        tif->tif_dir.td_resolutionunit)) {
          goto bad;
        }
      }
 /* jump:614 */      if (TIFFFieldSet(tif, FIELD_PAGENUMBER)) {
 /* jump:613 */        if (!TIFFWriteDirectoryTagShortArray(tif, &ndir, dir,
                                             TIFFTAG_PAGENUMBER, 2,
                                             &tif->tif_dir.td_pagenumber[0])) {
          goto bad;
        }
      }
 /* jump:629 */      if (TIFFFieldSet(tif, FIELD_STRIPBYTECOUNTS)) {
 /* jump:622 */        if (!isTiled(tif)) {
 /* jump:621 */          if (!TIFFWriteDirectoryTagLongLong8Array(
                  tif, &ndir, dir, TIFFTAG_STRIPBYTECOUNTS,
                  tif->tif_dir.td_nstrips, tif->tif_dir.td_stripbytecount)) {
            goto bad;
          }
        } else {
 /* jump:627 */          if (!TIFFWriteDirectoryTagLongLong8Array(
                  tif, &ndir, dir, TIFFTAG_TILEBYTECOUNTS,
                  tif->tif_dir.td_nstrips, tif->tif_dir.td_stripbytecount)) {
            goto bad;
          }
        }
      }
 /* jump:644 */      if (TIFFFieldSet(tif, FIELD_STRIPOFFSETS)) {
 /* jump:637 */        if (!isTiled(tif)) {
 /* jump:636 */          if (!TIFFWriteDirectoryTagLongLong8Array(
                  tif, &ndir, dir, TIFFTAG_STRIPOFFSETS,
                  tif->tif_dir.td_nstrips, tif->tif_dir.td_stripoffset)) {
            goto bad;
          }
        } else {
 /* jump:642 */          if (!TIFFWriteDirectoryTagLongLong8Array(
                  tif, &ndir, dir, TIFFTAG_TILEOFFSETS, tif->tif_dir.td_nstrips,
                  tif->tif_dir.td_stripoffset)) {
            goto bad;
          }
        }
      }
 /* jump:649 */      if (TIFFFieldSet(tif, FIELD_COLORMAP)) {
 /* jump:648 */        if (!TIFFWriteDirectoryTagColormap(tif, &ndir, dir)) {
          goto bad;
        }
      }
 /* jump:660 */      if (TIFFFieldSet(tif, FIELD_EXTRASAMPLES)) {
 /* jump:659 */        if (tif->tif_dir.td_extrasamples) {
          uint16 na;
          uint16 *nb;
          TIFFGetFieldDefaulted(tif, TIFFTAG_EXTRASAMPLES, &na, &nb);
 /* jump:658 */          if (!TIFFWriteDirectoryTagShortArray(tif, &ndir, dir,
                                               TIFFTAG_EXTRASAMPLES, na, nb)) {
            goto bad;
          }
        }
      }
 /* jump:667 */      if (TIFFFieldSet(tif, FIELD_SAMPLEFORMAT)) {
 /* jump:666 */        if (!TIFFWriteDirectoryTagShortPerSample(
                tif, &ndir, dir, TIFFTAG_SAMPLEFORMAT,
                tif->tif_dir.td_sampleformat)) {
          goto bad;
        }
      }
 /* jump:674 */      if (TIFFFieldSet(tif, FIELD_SMINSAMPLEVALUE)) {
 /* jump:673 */        if (!TIFFWriteDirectoryTagSampleformatPerSample(
                tif, &ndir, dir, TIFFTAG_SMINSAMPLEVALUE,
                tif->tif_dir.td_sminsamplevalue)) {
          goto bad;
        }
      }
 /* jump:681 */      if (TIFFFieldSet(tif, FIELD_SMAXSAMPLEVALUE)) {
 /* jump:680 */        if (!TIFFWriteDirectoryTagSampleformatPerSample(
                tif, &ndir, dir, TIFFTAG_SMAXSAMPLEVALUE,
                tif->tif_dir.td_smaxsamplevalue)) {
          goto bad;
        }
      }
 /* jump:687 */      if (TIFFFieldSet(tif, FIELD_IMAGEDEPTH)) {
 /* jump:686 */        if (!TIFFWriteDirectoryTagLong(tif, &ndir, dir, TIFFTAG_IMAGEDEPTH,
                                       tif->tif_dir.td_imagedepth)) {
          goto bad;
        }
      }
 /* jump:693 */      if (TIFFFieldSet(tif, FIELD_TILEDEPTH)) {
 /* jump:692 */        if (!TIFFWriteDirectoryTagLong(tif, &ndir, dir, TIFFTAG_TILEDEPTH,
                                       tif->tif_dir.td_tiledepth)) {
          goto bad;
        }
      }
 /* jump:700 */      if (TIFFFieldSet(tif, FIELD_HALFTONEHINTS)) {
 /* jump:699 */        if (!TIFFWriteDirectoryTagShortArray(
                tif, &ndir, dir, TIFFTAG_HALFTONEHINTS, 2,
                &tif->tif_dir.td_halftonehints[0])) {
          goto bad;
        }
      }
 /* jump:707 */      if (TIFFFieldSet(tif, FIELD_YCBCRSUBSAMPLING)) {
 /* jump:706 */        if (!TIFFWriteDirectoryTagShortArray(
                tif, &ndir, dir, TIFFTAG_YCBCRSUBSAMPLING, 2,
                &tif->tif_dir.td_ycbcrsubsampling[0])) {
          goto bad;
        }
      }
 /* jump:714 */      if (TIFFFieldSet(tif, FIELD_YCBCRPOSITIONING)) {
 /* jump:713 */        if (!TIFFWriteDirectoryTagShort(tif, &ndir, dir,
                                        TIFFTAG_YCBCRPOSITIONING,
                                        tif->tif_dir.td_ycbcrpositioning)) {
          goto bad;
        }
      }
 /* jump:719 */      if (TIFFFieldSet(tif, FIELD_TRANSFERFUNCTION)) {
 /* jump:718 */        if (!TIFFWriteDirectoryTagTransferfunction(tif, &ndir, dir)) {
          goto bad;
        }
      }
 /* jump:726 */      if (TIFFFieldSet(tif, FIELD_INKNAMES)) {
 /* jump:725 */        if (!TIFFWriteDirectoryTagAscii(tif, &ndir, dir, TIFFTAG_INKNAMES,
                                        tif->tif_dir.td_inknameslen,
                                        tif->tif_dir.td_inknames)) {
          goto bad;
        }
      }
 /* jump:731 */      if (TIFFFieldSet(tif, FIELD_SUBIFD)) {
 /* jump:730 */        if (!TIFFWriteDirectoryTagSubifd(tif, &ndir, dir)) {
          goto bad;
        }
      }
      {
        uint32 n;
 /* jump:792 */        for (n = 0; n < tif->tif_nfields; n++) {
          const TIFFField *o;
          o = tif->tif_fields[n];
 /* jump:791 */          if ((o->field_bit >= FIELD_CODEC) &&
              (TIFFFieldSet(tif, o->field_bit))) {
            switch (o->get_field_type) {
            case TIFF_SETGET_ASCII: {
              uint32 pa;
              char *pb;
              assert(o->field_type == TIFF_ASCII);
              assert(o->field_readcount == TIFF_VARIABLE);
              assert(o->field_passcount == 0);
              TIFFGetField(tif, o->field_tag, &pb);
              pa = (uint32)(strlen(pb));
 /* jump:751 */              if (!TIFFWriteDirectoryTagAscii(tif, &ndir, dir, o->field_tag, pa,
                                              pb)) {
                goto bad;
              }
            } break;
            case TIFF_SETGET_UINT16: {
              uint16 p;
              assert(o->field_type == TIFF_SHORT);
              assert(o->field_readcount == 1);
              assert(o->field_passcount == 0);
              TIFFGetField(tif, o->field_tag, &p);
 /* jump:762 */              if (!TIFFWriteDirectoryTagShort(tif, &ndir, dir, o->field_tag,
                                              p)) {
                goto bad;
              }
            } break;
            case TIFF_SETGET_UINT32: {
              uint32 p;
              assert(o->field_type == TIFF_LONG);
              assert(o->field_readcount == 1);
              assert(o->field_passcount == 0);
              TIFFGetField(tif, o->field_tag, &p);
 /* jump:773 */              if (!TIFFWriteDirectoryTagLong(tif, &ndir, dir, o->field_tag,
                                             p)) {
                goto bad;
              }
            } break;
            case TIFF_SETGET_C32_UINT8: {
              uint32 pa;
              void *pb;
              assert(o->field_type == TIFF_UNDEFINED);
              assert(o->field_readcount == TIFF_VARIABLE2);
              assert(o->field_passcount == 1);
              TIFFGetField(tif, o->field_tag, &pa, &pb);
 /* jump:785 */              if (!TIFFWriteDirectoryTagUndefinedArray(tif, &ndir, dir,
                                                       o->field_tag, pa, pb)) {
                goto bad;
              }
            } break;
            default:
              assert(0); /* we should never get here */
              break;
            }
          }
        }
      }
    }
 /* jump:945 */    for (m = 0; m < (uint32)(tif->tif_dir.td_customValueCount); m++) {
      switch (tif->tif_dir.td_customValues[m].info->field_type) {
      case TIFF_ASCII:
 /* jump:804 */        if (!TIFFWriteDirectoryTagAscii(
                tif, &ndir, dir,
                tif->tif_dir.td_customValues[m].info->field_tag,
                tif->tif_dir.td_customValues[m].count,
                tif->tif_dir.td_customValues[m].value)) {
          goto bad;
        }
        break;
      case TIFF_UNDEFINED:
 /* jump:813 */        if (!TIFFWriteDirectoryTagUndefinedArray(
                tif, &ndir, dir,
                tif->tif_dir.td_customValues[m].info->field_tag,
                tif->tif_dir.td_customValues[m].count,
                tif->tif_dir.td_customValues[m].value)) {
          goto bad;
        }
        break;
      case TIFF_BYTE:
 /* jump:822 */        if (!TIFFWriteDirectoryTagByteArray(
                tif, &ndir, dir,
                tif->tif_dir.td_customValues[m].info->field_tag,
                tif->tif_dir.td_customValues[m].count,
                tif->tif_dir.td_customValues[m].value)) {
          goto bad;
        }
        break;
      case TIFF_SBYTE:
 /* jump:831 */        if (!TIFFWriteDirectoryTagSbyteArray(
                tif, &ndir, dir,
                tif->tif_dir.td_customValues[m].info->field_tag,
                tif->tif_dir.td_customValues[m].count,
                tif->tif_dir.td_customValues[m].value)) {
          goto bad;
        }
        break;
      case TIFF_SHORT:
 /* jump:840 */        if (!TIFFWriteDirectoryTagShortArray(
                tif, &ndir, dir,
                tif->tif_dir.td_customValues[m].info->field_tag,
                tif->tif_dir.td_customValues[m].count,
                tif->tif_dir.td_customValues[m].value)) {
          goto bad;
        }
        break;
      case TIFF_SSHORT:
 /* jump:849 */        if (!TIFFWriteDirectoryTagSshortArray(
                tif, &ndir, dir,
                tif->tif_dir.td_customValues[m].info->field_tag,
                tif->tif_dir.td_customValues[m].count,
                tif->tif_dir.td_customValues[m].value)) {
          goto bad;
        }
        break;
      case TIFF_LONG:
 /* jump:858 */        if (!TIFFWriteDirectoryTagLongArray(
                tif, &ndir, dir,
                tif->tif_dir.td_customValues[m].info->field_tag,
                tif->tif_dir.td_customValues[m].count,
                tif->tif_dir.td_customValues[m].value)) {
          goto bad;
        }
        break;
      case TIFF_SLONG:
 /* jump:867 */        if (!TIFFWriteDirectoryTagSlongArray(
                tif, &ndir, dir,
                tif->tif_dir.td_customValues[m].info->field_tag,
                tif->tif_dir.td_customValues[m].count,
                tif->tif_dir.td_customValues[m].value)) {
          goto bad;
        }
        break;
      case TIFF_LONG8:
 /* jump:876 */        if (!TIFFWriteDirectoryTagLong8Array(
                tif, &ndir, dir,
                tif->tif_dir.td_customValues[m].info->field_tag,
                tif->tif_dir.td_customValues[m].count,
                tif->tif_dir.td_customValues[m].value)) {
          goto bad;
        }
        break;
      case TIFF_SLONG8:
 /* jump:885 */        if (!TIFFWriteDirectoryTagSlong8Array(
                tif, &ndir, dir,
                tif->tif_dir.td_customValues[m].info->field_tag,
                tif->tif_dir.td_customValues[m].count,
                tif->tif_dir.td_customValues[m].value)) {
          goto bad;
        }
        break;
      case TIFF_RATIONAL:
 /* jump:894 */        if (!TIFFWriteDirectoryTagRationalArray(
                tif, &ndir, dir,
                tif->tif_dir.td_customValues[m].info->field_tag,
                tif->tif_dir.td_customValues[m].count,
                tif->tif_dir.td_customValues[m].value)) {
          goto bad;
        }
        break;
      case TIFF_SRATIONAL:
 /* jump:903 */        if (!TIFFWriteDirectoryTagSrationalArray(
                tif, &ndir, dir,
                tif->tif_dir.td_customValues[m].info->field_tag,
                tif->tif_dir.td_customValues[m].count,
                tif->tif_dir.td_customValues[m].value)) {
          goto bad;
        }
        break;
      case TIFF_FLOAT:
 /* jump:912 */        if (!TIFFWriteDirectoryTagFloatArray(
                tif, &ndir, dir,
                tif->tif_dir.td_customValues[m].info->field_tag,
                tif->tif_dir.td_customValues[m].count,
                tif->tif_dir.td_customValues[m].value)) {
          goto bad;
        }
        break;
      case TIFF_DOUBLE:
 /* jump:921 */        if (!TIFFWriteDirectoryTagDoubleArray(
                tif, &ndir, dir,
                tif->tif_dir.td_customValues[m].info->field_tag,
                tif->tif_dir.td_customValues[m].count,
                tif->tif_dir.td_customValues[m].value)) {
          goto bad;
        }
        break;
      case TIFF_IFD:
 /* jump:930 */        if (!TIFFWriteDirectoryTagIfdArray(
                tif, &ndir, dir,
                tif->tif_dir.td_customValues[m].info->field_tag,
                tif->tif_dir.td_customValues[m].count,
                tif->tif_dir.td_customValues[m].value)) {
          goto bad;
        }
        break;
      case TIFF_IFD8:
 /* jump:939 */        if (!TIFFWriteDirectoryTagIfd8Array(
                tif, &ndir, dir,
                tif->tif_dir.td_customValues[m].info->field_tag,
                tif->tif_dir.td_customValues[m].count,
                tif->tif_dir.td_customValues[m].value)) {
          goto bad;
        }
        break;
      default:
        assert(0); /* we should never get here */
        break;
      }
    }
 /* jump:948 */    if (dir != NULL) {
      break;
    }
    dir = _TIFFmalloc(ndir * sizeof(TIFFDirEntry));
 /* jump:953 */    if (dir == NULL) {
      TIFFErrorExt(tif->tif_clientdata, module, "Out of memory");
      goto bad;
    }
 /* jump:958 */    if (isimage) {
 /* jump:957 */      if ((tif->tif_diroff == 0) && (!TIFFLinkDirectory(tif))) {
        goto bad;
      }
    } else {
      tif->tif_diroff = (TIFFSeekFile(tif, 0, SEEK_END) + 1) & (~1);
    }
 /* jump:963 */    if (pdiroff != NULL) {
      *pdiroff = tif->tif_diroff;
    }
 /* jump:966 */    if (!(tif->tif_flags & TIFF_BIGTIFF)) {
      dirsize = 2 + ndir * 12 + 4;
    } else {
      dirsize = 8 + ndir * 20 + 8;
    }
    tif->tif_dataoff = tif->tif_diroff + dirsize;
 /* jump:972 */    if (!(tif->tif_flags & TIFF_BIGTIFF)) {
      tif->tif_dataoff = (uint32)tif->tif_dataoff;
    }
 /* jump:978 */    if ((tif->tif_dataoff < tif->tif_diroff) ||
        (tif->tif_dataoff < (uint64)dirsize)) {
      TIFFErrorExt(tif->tif_clientdata, module,
                   "Maximum TIFF file size exceeded");
      goto bad;
    }
 /* jump:981 */    if (tif->tif_dataoff & 1) {
      tif->tif_dataoff++;
    }
 /* jump:984 */    if (isimage) {
      tif->tif_curdir++;
    }
  }
 /* jump:1002 */  if (isimage) {
 /* jump:1001 */    if (TIFFFieldSet(tif, FIELD_SUBIFD) && (tif->tif_subifdoff == 0)) {
      uint32 na;
      TIFFDirEntry *nb;
 /* jump:995 */      for (na = 0, nb = dir;; na++, nb++) {
        assert(na < ndir);
 /* jump:994 */        if (nb->tdir_tag == TIFFTAG_SUBIFD) {
          break;
        }
      }
 /* jump:998 */      if (!(tif->tif_flags & TIFF_BIGTIFF)) {
        tif->tif_subifdoff = tif->tif_diroff + 2 + na * 12 + 8;
      } else {
        tif->tif_subifdoff = tif->tif_diroff + 8 + na * 20 + 12;
      }
    }
  }
  dirmem = _TIFFmalloc(dirsize);
 /* jump:1007 */  if (dirmem == NULL) {
    TIFFErrorExt(tif->tif_clientdata, module, "Out of memory");
    goto bad;
  }
 /* jump:1039 */  if (!(tif->tif_flags & TIFF_BIGTIFF)) {
    uint8 *n;
    TIFFDirEntry *o;
    n = dirmem;
    *(uint16 *)n = ndir;
 /* jump:1015 */    if (tif->tif_flags & TIFF_SWAB) {
      TIFFSwabShort((uint16 *)n);
    }
    n += 2;
    o = dir;
 /* jump:1037 */    for (m = 0; m < ndir; m++) {
      *(uint16 *)n = o->tdir_tag;
 /* jump:1022 */      if (tif->tif_flags & TIFF_SWAB) {
        TIFFSwabShort((uint16 *)n);
      }
      n += 2;
      *(uint16 *)n = o->tdir_type;
 /* jump:1027 */      if (tif->tif_flags & TIFF_SWAB) {
        TIFFSwabShort((uint16 *)n);
      }
      n += 2;
      *(uint32 *)n = (uint32)o->tdir_count;
 /* jump:1032 */      if (tif->tif_flags & TIFF_SWAB) {
        TIFFSwabLong((uint32 *)n);
      }
      n += 4;
      _TIFFmemcpy(n, &o->tdir_offset, 4);
      n += 4;
      o++;
    }
    *(uint32 *)n = (uint32)tif->tif_nextdiroff;
  } else {
    uint8 *n;
    TIFFDirEntry *o;
    n = dirmem;
    *(uint64 *)n = ndir;
 /* jump:1046 */    if (tif->tif_flags & TIFF_SWAB) {
      TIFFSwabLong8((uint64 *)n);
    }
    n += 8;
    o = dir;
 /* jump:1068 */    for (m = 0; m < ndir; m++) {
      *(uint16 *)n = o->tdir_tag;
 /* jump:1053 */      if (tif->tif_flags & TIFF_SWAB) {
        TIFFSwabShort((uint16 *)n);
      }
      n += 2;
      *(uint16 *)n = o->tdir_type;
 /* jump:1058 */      if (tif->tif_flags & TIFF_SWAB) {
        TIFFSwabShort((uint16 *)n);
      }
      n += 2;
      *(uint64 *)n = o->tdir_count;
 /* jump:1063 */      if (tif->tif_flags & TIFF_SWAB) {
        TIFFSwabLong8((uint64 *)n);
      }
      n += 8;
      _TIFFmemcpy(n, &o->tdir_offset, 8);
      n += 8;
      o++;
    }
    *(uint64 *)n = tif->tif_nextdiroff;
  }
  _TIFFfree(dir);
  dir = NULL;
 /* jump:1076 */  if (!SeekOK(tif, tif->tif_diroff)) {
    TIFFErrorExt(tif->tif_clientdata, module, "IO error writing directory");
    goto bad;
  }
 /* jump:1080 */  if (!WriteOK(tif, dirmem, (tmsize_t)dirsize)) {
    TIFFErrorExt(tif->tif_clientdata, module, "IO error writing directory");
    goto bad;
  }
  _TIFFfree(dirmem);
 /* jump:1091 */  if (imagedone) {
    TIFFFreeDirectory(tif);
    tif->tif_flags &= ~TIFF_DIRTYDIRECT;
    (*tif->tif_cleanup)(tif);
    /*
     * Reset directory-related state for subsequent
     * directories.
     */
    TIFFCreateDirectory(tif);
  }
  return (1);
bad:
 /* jump:1096 */  if (dir != NULL) {
    _TIFFfree(dir);
  }
 /* jump:1099 */  if (dirmem != NULL) {
    _TIFFfree(dirmem);
  }
  return (0);
}

static int TIFFWriteDirectoryTagSampleformatPerSample(TIFF *tif, uint32 *ndir,
                                                      TIFFDirEntry *dir,
                                                      uint16 tag,
                                                      double value) {
  switch (tif->tif_dir.td_sampleformat) {
  case SAMPLEFORMAT_IEEEFP:
 /* jump:1112 */    if (tif->tif_dir.td_bitspersample <= 32) {
      return (TIFFWriteDirectoryTagFloatPerSample(tif, ndir, dir, tag,
                                                  (float)value));
    } else {
      return (TIFFWriteDirectoryTagDoublePerSample(tif, ndir, dir, tag, value));
    }
  case SAMPLEFORMAT_INT:
 /* jump:1119 */    if (tif->tif_dir.td_bitspersample <= 8) {
      return (TIFFWriteDirectoryTagSbytePerSample(tif, ndir, dir, tag,
                                                  (int8)value));
 /* jump:1122 */    } else if (tif->tif_dir.td_bitspersample <= 16) {
      return (TIFFWriteDirectoryTagSshortPerSample(tif, ndir, dir, tag,
                                                   (int16)value));
    } else {
      return (TIFFWriteDirectoryTagSlongPerSample(tif, ndir, dir, tag,
                                                  (int32)value));
    }
  case SAMPLEFORMAT_UINT:
 /* jump:1130 */    if (tif->tif_dir.td_bitspersample <= 8) {
      return (TIFFWriteDirectoryTagBytePerSample(tif, ndir, dir, tag,
                                                 (uint8)value));
 /* jump:1133 */    } else if (tif->tif_dir.td_bitspersample <= 16) {
      return (TIFFWriteDirectoryTagShortPerSample(tif, ndir, dir, tag,
                                                  (uint16)value));
    } else {
      return (TIFFWriteDirectoryTagLongPerSample(tif, ndir, dir, tag,
                                                 (uint32)value));
    }
  default:
    return (1);
  }
}

static int TIFFWriteDirectoryTagAscii(TIFF *tif, uint32 *ndir,
                                      TIFFDirEntry *dir, uint16 tag,
                                      uint32 count, char *value) {
 /* jump:1148 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  return (TIFFWriteDirectoryTagCheckedAscii(tif, ndir, dir, tag, count, value));
}

static int TIFFWriteDirectoryTagUndefinedArray(TIFF *tif, uint32 *ndir,
                                               TIFFDirEntry *dir, uint16 tag,
                                               uint32 count, uint8 *value) {
 /* jump:1158 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  return (TIFFWriteDirectoryTagCheckedUndefinedArray(tif, ndir, dir, tag, count,
                                                     value));
}

static int TIFFWriteDirectoryTagByte(TIFF *tif, uint32 *ndir, TIFFDirEntry *dir,
                                     uint16 tag, uint8 value) {
 /* jump:1168 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  return (TIFFWriteDirectoryTagCheckedByte(tif, ndir, dir, tag, value));
}

static int TIFFWriteDirectoryTagByteArray(TIFF *tif, uint32 *ndir,
                                          TIFFDirEntry *dir, uint16 tag,
                                          uint32 count, uint8 *value) {
 /* jump:1178 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  return (
      TIFFWriteDirectoryTagCheckedByteArray(tif, ndir, dir, tag, count, value));
}

static int TIFFWriteDirectoryTagBytePerSample(TIFF *tif, uint32 *ndir,
                                              TIFFDirEntry *dir, uint16 tag,
                                              uint8 value) {
  static const char module[] = "TIFFWriteDirectoryTagBytePerSample";
  uint8 *m;
  uint8 *na;
  uint16 nb;
  int o;
 /* jump:1194 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  m = _TIFFmalloc(tif->tif_dir.td_samplesperpixel * sizeof(uint8));
 /* jump:1199 */  if (m == NULL) {
    TIFFErrorExt(tif->tif_clientdata, module, "Out of memory");
    return (0);
  }
 /* jump:1202 */  for (na = m, nb = 0; nb < tif->tif_dir.td_samplesperpixel; na++, nb++) {
    *na = value;
  }
  o = TIFFWriteDirectoryTagCheckedByteArray(tif, ndir, dir, tag,
                                            tif->tif_dir.td_samplesperpixel, m);
  _TIFFfree(m);
  return (o);
}

static int TIFFWriteDirectoryTagSbyte(TIFF *tif, uint32 *ndir,
                                      TIFFDirEntry *dir, uint16 tag,
                                      int8 value) {
 /* jump:1215 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  return (TIFFWriteDirectoryTagCheckedSbyte(tif, ndir, dir, tag, value));
}

static int TIFFWriteDirectoryTagSbyteArray(TIFF *tif, uint32 *ndir,
                                           TIFFDirEntry *dir, uint16 tag,
                                           uint32 count, int8 *value) {
 /* jump:1225 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  return (TIFFWriteDirectoryTagCheckedSbyteArray(tif, ndir, dir, tag, count,
                                                 value));
}

static int TIFFWriteDirectoryTagSbytePerSample(TIFF *tif, uint32 *ndir,
                                               TIFFDirEntry *dir, uint16 tag,
                                               int8 value) {
  static const char module[] = "TIFFWriteDirectoryTagSbytePerSample";
  int8 *m;
  int8 *na;
  uint16 nb;
  int o;
 /* jump:1241 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  m = _TIFFmalloc(tif->tif_dir.td_samplesperpixel * sizeof(int8));
 /* jump:1246 */  if (m == NULL) {
    TIFFErrorExt(tif->tif_clientdata, module, "Out of memory");
    return (0);
  }
 /* jump:1249 */  for (na = m, nb = 0; nb < tif->tif_dir.td_samplesperpixel; na++, nb++) {
    *na = value;
  }
  o = TIFFWriteDirectoryTagCheckedSbyteArray(
      tif, ndir, dir, tag, tif->tif_dir.td_samplesperpixel, m);
  _TIFFfree(m);
  return (o);
}

static int TIFFWriteDirectoryTagShort(TIFF *tif, uint32 *ndir,
                                      TIFFDirEntry *dir, uint16 tag,
                                      uint16 value) {
 /* jump:1262 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  return (TIFFWriteDirectoryTagCheckedShort(tif, ndir, dir, tag, value));
}

static int TIFFWriteDirectoryTagShortArray(TIFF *tif, uint32 *ndir,
                                           TIFFDirEntry *dir, uint16 tag,
                                           uint32 count, uint16 *value) {
 /* jump:1272 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  return (TIFFWriteDirectoryTagCheckedShortArray(tif, ndir, dir, tag, count,
                                                 value));
}

static int TIFFWriteDirectoryTagShortPerSample(TIFF *tif, uint32 *ndir,
                                               TIFFDirEntry *dir, uint16 tag,
                                               uint16 value) {
  static const char module[] = "TIFFWriteDirectoryTagShortPerSample";
  uint16 *m;
  uint16 *na;
  uint16 nb;
  int o;
 /* jump:1288 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  m = _TIFFmalloc(tif->tif_dir.td_samplesperpixel * sizeof(uint16));
 /* jump:1293 */  if (m == NULL) {
    TIFFErrorExt(tif->tif_clientdata, module, "Out of memory");
    return (0);
  }
 /* jump:1296 */  for (na = m, nb = 0; nb < tif->tif_dir.td_samplesperpixel; na++, nb++) {
    *na = value;
  }
  o = TIFFWriteDirectoryTagCheckedShortArray(
      tif, ndir, dir, tag, tif->tif_dir.td_samplesperpixel, m);
  _TIFFfree(m);
  return (o);
}

static int TIFFWriteDirectoryTagSshort(TIFF *tif, uint32 *ndir,
                                       TIFFDirEntry *dir, uint16 tag,
                                       int16 value) {
 /* jump:1309 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  return (TIFFWriteDirectoryTagCheckedSshort(tif, ndir, dir, tag, value));
}

static int TIFFWriteDirectoryTagSshortArray(TIFF *tif, uint32 *ndir,
                                            TIFFDirEntry *dir, uint16 tag,
                                            uint32 count, int16 *value) {
 /* jump:1319 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  return (TIFFWriteDirectoryTagCheckedSshortArray(tif, ndir, dir, tag, count,
                                                  value));
}

static int TIFFWriteDirectoryTagSshortPerSample(TIFF *tif, uint32 *ndir,
                                                TIFFDirEntry *dir, uint16 tag,
                                                int16 value) {
  static const char module[] = "TIFFWriteDirectoryTagSshortPerSample";
  int16 *m;
  int16 *na;
  uint16 nb;
  int o;
 /* jump:1335 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  m = _TIFFmalloc(tif->tif_dir.td_samplesperpixel * sizeof(int16));
 /* jump:1340 */  if (m == NULL) {
    TIFFErrorExt(tif->tif_clientdata, module, "Out of memory");
    return (0);
  }
 /* jump:1343 */  for (na = m, nb = 0; nb < tif->tif_dir.td_samplesperpixel; na++, nb++) {
    *na = value;
  }
  o = TIFFWriteDirectoryTagCheckedSshortArray(
      tif, ndir, dir, tag, tif->tif_dir.td_samplesperpixel, m);
  _TIFFfree(m);
  return (o);
}

static int TIFFWriteDirectoryTagLong(TIFF *tif, uint32 *ndir, TIFFDirEntry *dir,
                                     uint16 tag, uint32 value) {
 /* jump:1355 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  return (TIFFWriteDirectoryTagCheckedLong(tif, ndir, dir, tag, value));
}

static int TIFFWriteDirectoryTagLongArray(TIFF *tif, uint32 *ndir,
                                          TIFFDirEntry *dir, uint16 tag,
                                          uint32 count, uint32 *value) {
 /* jump:1365 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  return (
      TIFFWriteDirectoryTagCheckedLongArray(tif, ndir, dir, tag, count, value));
}

static int TIFFWriteDirectoryTagLongPerSample(TIFF *tif, uint32 *ndir,
                                              TIFFDirEntry *dir, uint16 tag,
                                              uint32 value) {
  static const char module[] = "TIFFWriteDirectoryTagLongPerSample";
  uint32 *m;
  uint32 *na;
  uint16 nb;
  int o;
 /* jump:1381 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  m = _TIFFmalloc(tif->tif_dir.td_samplesperpixel * sizeof(uint32));
 /* jump:1386 */  if (m == NULL) {
    TIFFErrorExt(tif->tif_clientdata, module, "Out of memory");
    return (0);
  }
 /* jump:1389 */  for (na = m, nb = 0; nb < tif->tif_dir.td_samplesperpixel; na++, nb++) {
    *na = value;
  }
  o = TIFFWriteDirectoryTagCheckedLongArray(tif, ndir, dir, tag,
                                            tif->tif_dir.td_samplesperpixel, m);
  _TIFFfree(m);
  return (o);
}

static int TIFFWriteDirectoryTagSlong(TIFF *tif, uint32 *ndir,
                                      TIFFDirEntry *dir, uint16 tag,
                                      int32 value) {
 /* jump:1402 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  return (TIFFWriteDirectoryTagCheckedSlong(tif, ndir, dir, tag, value));
}

static int TIFFWriteDirectoryTagSlongArray(TIFF *tif, uint32 *ndir,
                                           TIFFDirEntry *dir, uint16 tag,
                                           uint32 count, int32 *value) {
 /* jump:1412 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  return (TIFFWriteDirectoryTagCheckedSlongArray(tif, ndir, dir, tag, count,
                                                 value));
}

static int TIFFWriteDirectoryTagSlongPerSample(TIFF *tif, uint32 *ndir,
                                               TIFFDirEntry *dir, uint16 tag,
                                               int32 value) {
  static const char module[] = "TIFFWriteDirectoryTagSlongPerSample";
  int32 *m;
  int32 *na;
  uint16 nb;
  int o;
 /* jump:1428 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  m = _TIFFmalloc(tif->tif_dir.td_samplesperpixel * sizeof(int32));
 /* jump:1433 */  if (m == NULL) {
    TIFFErrorExt(tif->tif_clientdata, module, "Out of memory");
    return (0);
  }
 /* jump:1436 */  for (na = m, nb = 0; nb < tif->tif_dir.td_samplesperpixel; na++, nb++) {
    *na = value;
  }
  o = TIFFWriteDirectoryTagCheckedSlongArray(
      tif, ndir, dir, tag, tif->tif_dir.td_samplesperpixel, m);
  _TIFFfree(m);
  return (o);
}

static int TIFFWriteDirectoryTagLong8(TIFF *tif, uint32 *ndir,
                                      TIFFDirEntry *dir, uint16 tag,
                                      uint64 value) {
 /* jump:1449 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  return (TIFFWriteDirectoryTagCheckedLong8(tif, ndir, dir, tag, value));
}

static int TIFFWriteDirectoryTagLong8Array(TIFF *tif, uint32 *ndir,
                                           TIFFDirEntry *dir, uint16 tag,
                                           uint32 count, uint64 *value) {
 /* jump:1459 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  return (TIFFWriteDirectoryTagCheckedLong8Array(tif, ndir, dir, tag, count,
                                                 value));
}

static int TIFFWriteDirectoryTagSlong8(TIFF *tif, uint32 *ndir,
                                       TIFFDirEntry *dir, uint16 tag,
                                       int64 value) {
 /* jump:1470 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  return (TIFFWriteDirectoryTagCheckedSlong8(tif, ndir, dir, tag, value));
}

static int TIFFWriteDirectoryTagSlong8Array(TIFF *tif, uint32 *ndir,
                                            TIFFDirEntry *dir, uint16 tag,
                                            uint32 count, int64 *value) {
 /* jump:1480 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  return (TIFFWriteDirectoryTagCheckedSlong8Array(tif, ndir, dir, tag, count,
                                                  value));
}

static int TIFFWriteDirectoryTagRational(TIFF *tif, uint32 *ndir,
                                         TIFFDirEntry *dir, uint16 tag,
                                         double value) {
 /* jump:1491 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  return (TIFFWriteDirectoryTagCheckedRational(tif, ndir, dir, tag, value));
}

static int TIFFWriteDirectoryTagRationalArray(TIFF *tif, uint32 *ndir,
                                              TIFFDirEntry *dir, uint16 tag,
                                              uint32 count, float *value) {
 /* jump:1501 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  return (TIFFWriteDirectoryTagCheckedRationalArray(tif, ndir, dir, tag, count,
                                                    value));
}

static int TIFFWriteDirectoryTagSrationalArray(TIFF *tif, uint32 *ndir,
                                               TIFFDirEntry *dir, uint16 tag,
                                               uint32 count, float *value) {
 /* jump:1512 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  return (TIFFWriteDirectoryTagCheckedSrationalArray(tif, ndir, dir, tag, count,
                                                     value));
}

static int TIFFWriteDirectoryTagFloat(TIFF *tif, uint32 *ndir,
                                      TIFFDirEntry *dir, uint16 tag,
                                      float value) {
 /* jump:1523 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  return (TIFFWriteDirectoryTagCheckedFloat(tif, ndir, dir, tag, value));
}

static int TIFFWriteDirectoryTagFloatArray(TIFF *tif, uint32 *ndir,
                                           TIFFDirEntry *dir, uint16 tag,
                                           uint32 count, float *value) {
 /* jump:1533 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  return (TIFFWriteDirectoryTagCheckedFloatArray(tif, ndir, dir, tag, count,
                                                 value));
}

static int TIFFWriteDirectoryTagFloatPerSample(TIFF *tif, uint32 *ndir,
                                               TIFFDirEntry *dir, uint16 tag,
                                               float value) {
  static const char module[] = "TIFFWriteDirectoryTagFloatPerSample";
  float *m;
  float *na;
  uint16 nb;
  int o;
 /* jump:1549 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  m = _TIFFmalloc(tif->tif_dir.td_samplesperpixel * sizeof(float));
 /* jump:1554 */  if (m == NULL) {
    TIFFErrorExt(tif->tif_clientdata, module, "Out of memory");
    return (0);
  }
 /* jump:1557 */  for (na = m, nb = 0; nb < tif->tif_dir.td_samplesperpixel; na++, nb++) {
    *na = value;
  }
  o = TIFFWriteDirectoryTagCheckedFloatArray(
      tif, ndir, dir, tag, tif->tif_dir.td_samplesperpixel, m);
  _TIFFfree(m);
  return (o);
}

static int TIFFWriteDirectoryTagDouble(TIFF *tif, uint32 *ndir,
                                       TIFFDirEntry *dir, uint16 tag,
                                       double value) {
 /* jump:1570 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  return (TIFFWriteDirectoryTagCheckedDouble(tif, ndir, dir, tag, value));
}

static int TIFFWriteDirectoryTagDoubleArray(TIFF *tif, uint32 *ndir,
                                            TIFFDirEntry *dir, uint16 tag,
                                            uint32 count, double *value) {
 /* jump:1580 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  return (TIFFWriteDirectoryTagCheckedDoubleArray(tif, ndir, dir, tag, count,
                                                  value));
}

static int TIFFWriteDirectoryTagDoublePerSample(TIFF *tif, uint32 *ndir,
                                                TIFFDirEntry *dir, uint16 tag,
                                                double value) {
  static const char module[] = "TIFFWriteDirectoryTagDoublePerSample";
  double *m;
  double *na;
  uint16 nb;
  int o;
 /* jump:1596 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  m = _TIFFmalloc(tif->tif_dir.td_samplesperpixel * sizeof(double));
 /* jump:1601 */  if (m == NULL) {
    TIFFErrorExt(tif->tif_clientdata, module, "Out of memory");
    return (0);
  }
 /* jump:1604 */  for (na = m, nb = 0; nb < tif->tif_dir.td_samplesperpixel; na++, nb++) {
    *na = value;
  }
  o = TIFFWriteDirectoryTagCheckedDoubleArray(
      tif, ndir, dir, tag, tif->tif_dir.td_samplesperpixel, m);
  _TIFFfree(m);
  return (o);
}

static int TIFFWriteDirectoryTagIfdArray(TIFF *tif, uint32 *ndir,
                                         TIFFDirEntry *dir, uint16 tag,
                                         uint32 count, uint32 *value) {
 /* jump:1617 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  return (
      TIFFWriteDirectoryTagCheckedIfdArray(tif, ndir, dir, tag, count, value));
}

static int TIFFWriteDirectoryTagIfd8Array(TIFF *tif, uint32 *ndir,
                                          TIFFDirEntry *dir, uint16 tag,
                                          uint32 count, uint64 *value) {
 /* jump:1628 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  return (
      TIFFWriteDirectoryTagCheckedIfd8Array(tif, ndir, dir, tag, count, value));
}

static int TIFFWriteDirectoryTagShortLong(TIFF *tif, uint32 *ndir,
                                          TIFFDirEntry *dir, uint16 tag,
                                          uint32 value) {
 /* jump:1639 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
 /* jump:1643 */  if (value <= 0xFFFF) {
    return (
        TIFFWriteDirectoryTagCheckedShort(tif, ndir, dir, tag, (uint16)value));
  } else {
    return (TIFFWriteDirectoryTagCheckedLong(tif, ndir, dir, tag, value));
  }
}

/************************************************************************/
/*                TIFFWriteDirectoryTagLongLong8Array()                 */
/*                                                                      */
/*      Write out LONG8 array as LONG8 for BigTIFF or LONG for          */
/*      Classic TIFF with some checking.                                */
/************************************************************************/

static int TIFFWriteDirectoryTagLongLong8Array(TIFF *tif, uint32 *ndir,
                                               TIFFDirEntry *dir, uint16 tag,
                                               uint32 count, uint64 *value) {
  static const char module[] = "TIFFWriteDirectoryTagLongLong8Array";
  uint64 *ma;
  uint32 mb;
  uint32 *p;
  uint32 *q;
  int o;

  /* is this just a counting pass? */
 /* jump:1669 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }

  /* We always write LONG8 for BigTIFF, no checking needed. */
 /* jump:1675 */  if (tif->tif_flags & TIFF_BIGTIFF) {
    return TIFFWriteDirectoryTagCheckedLong8Array(tif, ndir, dir, tag, count,
                                                  value);
  }

  /*
  ** For classic tiff we want to verify everything is in range for LONG
  ** and convert to long format.
  */

  p = _TIFFmalloc(count * sizeof(uint32));
 /* jump:1686 */  if (p == NULL) {
    TIFFErrorExt(tif->tif_clientdata, module, "Out of memory");
    return (0);
  }

 /* jump:1697 */  for (q = p, ma = value, mb = 0; mb < count; ma++, mb++, q++) {
 /* jump:1695 */    if (*ma > 0xFFFFFFFF) {
      TIFFErrorExt(tif->tif_clientdata, module,
                   "Attempt to write value larger than 0xFFFFFFFF in Classic "
                   "TIFF file.");
      _TIFFfree(p);
      return (0);
    }
    *q = (uint32)(*ma);
  }

  o = TIFFWriteDirectoryTagCheckedLongArray(tif, ndir, dir, tag, count, p);
  _TIFFfree(p);

  return (o);
}

static int TIFFWriteDirectoryTagShortLongLong8Array(TIFF *tif, uint32 *ndir,
                                                    TIFFDirEntry *dir,
                                                    uint16 tag, uint32 count,
                                                    uint64 *value) {
  static const char module[] = "TIFFWriteDirectoryTagShortLongLong8Array";
  uint64 *ma;
  uint32 mb;
  uint8 n;
  int o;
 /* jump:1717 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  n = 0;
 /* jump:1727 */  for (ma = value, mb = 0; mb < count; ma++, mb++) {
 /* jump:1722 */    if ((n == 0) && (*ma > 0xFFFF)) {
      n = 1;
    }
 /* jump:1726 */    if ((n == 1) && (*ma > 0xFFFFFFFF)) {
      n = 2;
      break;
    }
  }
 /* jump:1741 */  if (n == 0) {
    uint16 *p;
    uint16 *q;
    p = _TIFFmalloc(count * sizeof(uint16));
 /* jump:1735 */    if (p == NULL) {
      TIFFErrorExt(tif->tif_clientdata, module, "Out of memory");
      return (0);
    }
 /* jump:1738 */    for (ma = value, mb = 0, q = p; mb < count; ma++, mb++, q++) {
      *q = (uint16)(*ma);
    }
    o = TIFFWriteDirectoryTagCheckedShortArray(tif, ndir, dir, tag, count, p);
    _TIFFfree(p);
 /* jump:1754 */  } else if (n == 1) {
    uint32 *p;
    uint32 *q;
    p = _TIFFmalloc(count * sizeof(uint32));
 /* jump:1748 */    if (p == NULL) {
      TIFFErrorExt(tif->tif_clientdata, module, "Out of memory");
      return (0);
    }
 /* jump:1751 */    for (ma = value, mb = 0, q = p; mb < count; ma++, mb++, q++) {
      *q = (uint32)(*ma);
    }
    o = TIFFWriteDirectoryTagCheckedLongArray(tif, ndir, dir, tag, count, p);
    _TIFFfree(p);
  } else {
    assert(n == 2);
    o = TIFFWriteDirectoryTagCheckedLong8Array(tif, ndir, dir, tag, count,
                                               value);
  }
  return (o);
}

static int TIFFWriteDirectoryTagColormap(TIFF *tif, uint32 *ndir,
                                         TIFFDirEntry *dir) {
  static const char module[] = "TIFFWriteDirectoryTagColormap";
  uint32 m;
  uint16 *n;
  int o;
 /* jump:1771 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  m = (1 << tif->tif_dir.td_bitspersample);
  n = _TIFFmalloc(3 * m * sizeof(uint16));
 /* jump:1777 */  if (n == NULL) {
    TIFFErrorExt(tif->tif_clientdata, module, "Out of memory");
    return (0);
  }
  _TIFFmemcpy(&n[0], tif->tif_dir.td_colormap[0], m * sizeof(uint16));
  _TIFFmemcpy(&n[m], tif->tif_dir.td_colormap[1], m * sizeof(uint16));
  _TIFFmemcpy(&n[2 * m], tif->tif_dir.td_colormap[2], m * sizeof(uint16));
  o = TIFFWriteDirectoryTagCheckedShortArray(tif, ndir, dir, TIFFTAG_COLORMAP,
                                             3 * m, n);
  _TIFFfree(n);
  return (o);
}

static int TIFFWriteDirectoryTagTransferfunction(TIFF *tif, uint32 *ndir,
                                                 TIFFDirEntry *dir) {
  static const char module[] = "TIFFWriteDirectoryTagTransferfunction";
  uint32 m;
  uint16 n;
  uint16 *o;
  int p;
 /* jump:1797 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  m = (1 << tif->tif_dir.td_bitspersample);
  n = tif->tif_dir.td_samplesperpixel - tif->tif_dir.td_extrasamples;
  /*
   * Check if the table can be written as a single column,
   * or if it must be written as 3 columns.  Note that we
   * write a 3-column tag if there are 2 samples/pixel and
   * a single column of data won't suffice--hmm.
   */
 /* jump:1808 */  if (n > 3) {
    n = 3;
  }
 /* jump:1814 */  if (n == 3) {
 /* jump:1813 */    if (!_TIFFmemcmp(tif->tif_dir.td_transferfunction[0],
                     tif->tif_dir.td_transferfunction[2], m * sizeof(uint16))) {
      n = 2;
    }
  }
 /* jump:1820 */  if (n == 2) {
 /* jump:1819 */    if (!_TIFFmemcmp(tif->tif_dir.td_transferfunction[0],
                     tif->tif_dir.td_transferfunction[1], m * sizeof(uint16))) {
      n = 1;
    }
  }
 /* jump:1823 */  if (n == 0) {
    n = 1;
  }
  o = _TIFFmalloc(n * m * sizeof(uint16));
 /* jump:1828 */  if (o == NULL) {
    TIFFErrorExt(tif->tif_clientdata, module, "Out of memory");
    return (0);
  }
  _TIFFmemcpy(&o[0], tif->tif_dir.td_transferfunction[0], m * sizeof(uint16));
 /* jump:1832 */  if (n > 1) {
    _TIFFmemcpy(&o[m], tif->tif_dir.td_transferfunction[1], m * sizeof(uint16));
  }
 /* jump:1836 */  if (n > 2) {
    _TIFFmemcpy(&o[2 * m], tif->tif_dir.td_transferfunction[2],
                m * sizeof(uint16));
  }
  p = TIFFWriteDirectoryTagCheckedShortArray(
      tif, ndir, dir, TIFFTAG_TRANSFERFUNCTION, n * m, o);
  _TIFFfree(o);
  return (p);
}

static int TIFFWriteDirectoryTagSubifd(TIFF *tif, uint32 *ndir,
                                       TIFFDirEntry *dir) {
  static const char module[] = "TIFFWriteDirectoryTagSubifd";
  uint64 m;
  int n;
 /* jump:1850 */  if (tif->tif_dir.td_nsubifd == 0) {
    return (1);
  }
 /* jump:1854 */  if (dir == NULL) {
    (*ndir)++;
    return (1);
  }
  m = tif->tif_dataoff;
 /* jump:1875 */  if (!(tif->tif_flags & TIFF_BIGTIFF)) {
    uint32 *o;
    uint64 *pa;
    uint32 *pb;
    uint16 p;
    o = _TIFFmalloc(tif->tif_dir.td_nsubifd * sizeof(uint32));
 /* jump:1865 */    if (o == NULL) {
      TIFFErrorExt(tif->tif_clientdata, module, "Out of memory");
      return (0);
    }
    pa = tif->tif_dir.td_subifd;
    pb = o;
 /* jump:1871 */    for (p = 0; p < tif->tif_dir.td_nsubifd; p++) {
      assert(*pa <= 0xFFFFFFFFUL);
      *pb++ = (uint32)(*pa++);
    }
    n = TIFFWriteDirectoryTagCheckedIfdArray(tif, ndir, dir, TIFFTAG_SUBIFD,
                                             tif->tif_dir.td_nsubifd, o);
    _TIFFfree(o);
  } else {
    n = TIFFWriteDirectoryTagCheckedIfd8Array(tif, ndir, dir, TIFFTAG_SUBIFD,
                                              tif->tif_dir.td_nsubifd,
                                              tif->tif_dir.td_subifd);
  }
 /* jump:1882 */  if (!n) {
    return (0);
  }
  /*
   * Total hack: if this directory includes a SubIFD
   * tag then force the next <n> directories to be
   * written as ``sub directories'' of this one.  This
   * is used to write things like thumbnails and
   * image masks that one wants to keep out of the
   * normal directory linkage access mechanism.
   */
  tif->tif_flags |= TIFF_INSUBIFD;
  tif->tif_nsubifd = tif->tif_dir.td_nsubifd;
 /* jump:1895 */  if (tif->tif_dir.td_nsubifd == 1) {
    tif->tif_subifdoff = 0;
  } else {
    tif->tif_subifdoff = m;
  }
  return (1);
}

static int TIFFWriteDirectoryTagCheckedAscii(TIFF *tif, uint32 *ndir,
                                             TIFFDirEntry *dir, uint16 tag,
                                             uint32 count, char *value) {
  assert(sizeof(char) == 1);
  return (TIFFWriteDirectoryTagData(tif, ndir, dir, tag, TIFF_ASCII, count,
                                    count, value));
}

static int TIFFWriteDirectoryTagCheckedUndefinedArray(TIFF *tif, uint32 *ndir,
                                                      TIFFDirEntry *dir,
                                                      uint16 tag, uint32 count,
                                                      uint8 *value) {
  assert(sizeof(uint8) == 1);
  return (TIFFWriteDirectoryTagData(tif, ndir, dir, tag, TIFF_UNDEFINED, count,
                                    count, value));
}

static int TIFFWriteDirectoryTagCheckedByte(TIFF *tif, uint32 *ndir,
                                            TIFFDirEntry *dir, uint16 tag,
                                            uint8 value) {
  assert(sizeof(uint8) == 1);
  return (
      TIFFWriteDirectoryTagData(tif, ndir, dir, tag, TIFF_BYTE, 1, 1, &value));
}

static int TIFFWriteDirectoryTagCheckedByteArray(TIFF *tif, uint32 *ndir,
                                                 TIFFDirEntry *dir, uint16 tag,
                                                 uint32 count, uint8 *value) {
  assert(sizeof(uint8) == 1);
  return (TIFFWriteDirectoryTagData(tif, ndir, dir, tag, TIFF_BYTE, count,
                                    count, value));
}

static int TIFFWriteDirectoryTagCheckedSbyte(TIFF *tif, uint32 *ndir,
                                             TIFFDirEntry *dir, uint16 tag,
                                             int8 value) {
  assert(sizeof(int8) == 1);
  return (
      TIFFWriteDirectoryTagData(tif, ndir, dir, tag, TIFF_SBYTE, 1, 1, &value));
}

static int TIFFWriteDirectoryTagCheckedSbyteArray(TIFF *tif, uint32 *ndir,
                                                  TIFFDirEntry *dir, uint16 tag,
                                                  uint32 count, int8 *value) {
  assert(sizeof(int8) == 1);
  return (TIFFWriteDirectoryTagData(tif, ndir, dir, tag, TIFF_SBYTE, count,
                                    count, value));
}

static int TIFFWriteDirectoryTagCheckedShort(TIFF *tif, uint32 *ndir,
                                             TIFFDirEntry *dir, uint16 tag,
                                             uint16 value) {
  uint16 m;
  assert(sizeof(uint16) == 2);
  m = value;
 /* jump:1958 */  if (tif->tif_flags & TIFF_SWAB) {
    TIFFSwabShort(&m);
  }
  return (TIFFWriteDirectoryTagData(tif, ndir, dir, tag, TIFF_SHORT, 1, 2, &m));
}

static int TIFFWriteDirectoryTagCheckedShortArray(TIFF *tif, uint32 *ndir,
                                                  TIFFDirEntry *dir, uint16 tag,
                                                  uint32 count, uint16 *value) {
  assert(count < 0x80000000);
  assert(sizeof(uint16) == 2);
 /* jump:1969 */  if (tif->tif_flags & TIFF_SWAB) {
    TIFFSwabArrayOfShort(value, count);
  }
  return (TIFFWriteDirectoryTagData(tif, ndir, dir, tag, TIFF_SHORT, count,
                                    count * 2, value));
}

static int TIFFWriteDirectoryTagCheckedSshort(TIFF *tif, uint32 *ndir,
                                              TIFFDirEntry *dir, uint16 tag,
                                              int16 value) {
  int16 m;
  assert(sizeof(int16) == 2);
  m = value;
 /* jump:1982 */  if (tif->tif_flags & TIFF_SWAB) {
    TIFFSwabShort((uint16 *)(&m));
  }
  return (
      TIFFWriteDirectoryTagData(tif, ndir, dir, tag, TIFF_SSHORT, 1, 2, &m));
}

static int TIFFWriteDirectoryTagCheckedSshortArray(TIFF *tif, uint32 *ndir,
                                                   TIFFDirEntry *dir,
                                                   uint16 tag, uint32 count,
                                                   int16 *value) {
  assert(count < 0x80000000);
  assert(sizeof(int16) == 2);
 /* jump:1995 */  if (tif->tif_flags & TIFF_SWAB) {
    TIFFSwabArrayOfShort((uint16 *)value, count);
  }
  return (TIFFWriteDirectoryTagData(tif, ndir, dir, tag, TIFF_SSHORT, count,
                                    count * 2, value));
}

static int TIFFWriteDirectoryTagCheckedLong(TIFF *tif, uint32 *ndir,
                                            TIFFDirEntry *dir, uint16 tag,
                                            uint32 value) {
  uint32 m;
  assert(sizeof(uint32) == 4);
  m = value;
 /* jump:2008 */  if (tif->tif_flags & TIFF_SWAB) {
    TIFFSwabLong(&m);
  }
  return (TIFFWriteDirectoryTagData(tif, ndir, dir, tag, TIFF_LONG, 1, 4, &m));
}

static int TIFFWriteDirectoryTagCheckedLongArray(TIFF *tif, uint32 *ndir,
                                                 TIFFDirEntry *dir, uint16 tag,
                                                 uint32 count, uint32 *value) {
  assert(count < 0x40000000);
  assert(sizeof(uint32) == 4);
 /* jump:2019 */  if (tif->tif_flags & TIFF_SWAB) {
    TIFFSwabArrayOfLong(value, count);
  }
  return (TIFFWriteDirectoryTagData(tif, ndir, dir, tag, TIFF_LONG, count,
                                    count * 4, value));
}

static int TIFFWriteDirectoryTagCheckedSlong(TIFF *tif, uint32 *ndir,
                                             TIFFDirEntry *dir, uint16 tag,
                                             int32 value) {
  int32 m;
  assert(sizeof(int32) == 4);
  m = value;
 /* jump:2032 */  if (tif->tif_flags & TIFF_SWAB) {
    TIFFSwabLong((uint32 *)(&m));
  }
  return (TIFFWriteDirectoryTagData(tif, ndir, dir, tag, TIFF_SLONG, 1, 4, &m));
}

static int TIFFWriteDirectoryTagCheckedSlongArray(TIFF *tif, uint32 *ndir,
                                                  TIFFDirEntry *dir, uint16 tag,
                                                  uint32 count, int32 *value) {
  assert(count < 0x40000000);
  assert(sizeof(int32) == 4);
 /* jump:2043 */  if (tif->tif_flags & TIFF_SWAB) {
    TIFFSwabArrayOfLong((uint32 *)value, count);
  }
  return (TIFFWriteDirectoryTagData(tif, ndir, dir, tag, TIFF_SLONG, count,
                                    count * 4, value));
}

static int TIFFWriteDirectoryTagCheckedLong8(TIFF *tif, uint32 *ndir,
                                             TIFFDirEntry *dir, uint16 tag,
                                             uint64 value) {
  uint64 m;
  assert(sizeof(uint64) == 8);
  assert(tif->tif_flags & TIFF_BIGTIFF);
  m = value;
 /* jump:2057 */  if (tif->tif_flags & TIFF_SWAB) {
    TIFFSwabLong8(&m);
  }
  return (TIFFWriteDirectoryTagData(tif, ndir, dir, tag, TIFF_LONG8, 1, 8, &m));
}

static int TIFFWriteDirectoryTagCheckedLong8Array(TIFF *tif, uint32 *ndir,
                                                  TIFFDirEntry *dir, uint16 tag,
                                                  uint32 count, uint64 *value) {
  assert(count < 0x20000000);
  assert(sizeof(uint64) == 8);
  assert(tif->tif_flags & TIFF_BIGTIFF);
 /* jump:2069 */  if (tif->tif_flags & TIFF_SWAB) {
    TIFFSwabArrayOfLong8(value, count);
  }
  return (TIFFWriteDirectoryTagData(tif, ndir, dir, tag, TIFF_LONG8, count,
                                    count * 8, value));
}

static int TIFFWriteDirectoryTagCheckedSlong8(TIFF *tif, uint32 *ndir,
                                              TIFFDirEntry *dir, uint16 tag,
                                              int64 value) {
  int64 m;
  assert(sizeof(int64) == 8);
  assert(tif->tif_flags & TIFF_BIGTIFF);
  m = value;
 /* jump:2083 */  if (tif->tif_flags & TIFF_SWAB) {
    TIFFSwabLong8((uint64 *)(&m));
  }
  return (
      TIFFWriteDirectoryTagData(tif, ndir, dir, tag, TIFF_SLONG8, 1, 8, &m));
}

static int TIFFWriteDirectoryTagCheckedSlong8Array(TIFF *tif, uint32 *ndir,
                                                   TIFFDirEntry *dir,
                                                   uint16 tag, uint32 count,
                                                   int64 *value) {
  assert(count < 0x20000000);
  assert(sizeof(int64) == 8);
  assert(tif->tif_flags & TIFF_BIGTIFF);
 /* jump:2097 */  if (tif->tif_flags & TIFF_SWAB) {
    TIFFSwabArrayOfLong8((uint64 *)value, count);
  }
  return (TIFFWriteDirectoryTagData(tif, ndir, dir, tag, TIFF_SLONG8, count,
                                    count * 8, value));
}

static int TIFFWriteDirectoryTagCheckedRational(TIFF *tif, uint32 *ndir,
                                                TIFFDirEntry *dir, uint16 tag,
                                                double value) {
  uint32 m[2];
  assert(value >= 0.0);
  assert(sizeof(uint32) == 4);
 /* jump:2111 */  if (value <= 0.0) {
    m[0] = 0;
    m[1] = 1;
 /* jump:2114 */  } else if (value == (double)(uint32)value) {
    m[0] = (uint32)value;
    m[1] = 1;
 /* jump:2117 */  } else if (value < 1.0) {
    m[0] = (uint32)(value * 0xFFFFFFFF);
    m[1] = 0xFFFFFFFF;
  } else {
    m[0] = 0xFFFFFFFF;
    m[1] = (uint32)(0xFFFFFFFF / value);
  }
 /* jump:2124 */  if (tif->tif_flags & TIFF_SWAB) {
    TIFFSwabLong(&m[0]);
    TIFFSwabLong(&m[1]);
  }
  return (TIFFWriteDirectoryTagData(tif, ndir, dir, tag, TIFF_RATIONAL, 1, 8,
                                    &m[0]));
}

static int TIFFWriteDirectoryTagCheckedRationalArray(TIFF *tif, uint32 *ndir,
                                                     TIFFDirEntry *dir,
                                                     uint16 tag, uint32 count,
                                                     float *value) {
  static const char module[] = "TIFFWriteDirectoryTagCheckedRationalArray";
  uint32 *m;
  float *na;
  uint32 *nb;
  uint32 nc;
  int o;
  assert(sizeof(uint32) == 4);
  m = _TIFFmalloc(count * 2 * sizeof(uint32));
 /* jump:2144 */  if (m == NULL) {
    TIFFErrorExt(tif->tif_clientdata, module, "Out of memory");
    return (0);
  }
 /* jump:2159 */  for (na = value, nb = m, nc = 0; nc < count; na++, nb += 2, nc++) {
 /* jump:2149 */    if (*na <= 0.0) {
      nb[0] = 0;
      nb[1] = 1;
 /* jump:2152 */    } else if (*na == (float)(uint32)(*na)) {
      nb[0] = (uint32)(*na);
      nb[1] = 1;
 /* jump:2155 */    } else if (*na < 1.0) {
      nb[0] = (uint32)((*na) * 0xFFFFFFFF);
      nb[1] = 0xFFFFFFFF;
    } else {
      nb[0] = 0xFFFFFFFF;
      nb[1] = (uint32)(0xFFFFFFFF / (*na));
    }
  }
 /* jump:2162 */  if (tif->tif_flags & TIFF_SWAB) {
    TIFFSwabArrayOfLong(m, count * 2);
  }
  o = TIFFWriteDirectoryTagData(tif, ndir, dir, tag, TIFF_RATIONAL, count,
                                count * 8, &m[0]);
  _TIFFfree(m);
  return (o);
}

static int TIFFWriteDirectoryTagCheckedSrationalArray(TIFF *tif, uint32 *ndir,
                                                      TIFFDirEntry *dir,
                                                      uint16 tag, uint32 count,
                                                      float *value) {
  static const char module[] = "TIFFWriteDirectoryTagCheckedSrationalArray";
  int32 *m;
  float *na;
  int32 *nb;
  uint32 nc;
  int o;
  assert(sizeof(int32) == 4);
  m = _TIFFmalloc(count * 2 * sizeof(int32));
 /* jump:2184 */  if (m == NULL) {
    TIFFErrorExt(tif->tif_clientdata, module, "Out of memory");
    return (0);
  }
 /* jump:2209 */  for (na = value, nb = m, nc = 0; nc < count; na++, nb += 2, nc++) {
 /* jump:2197 */    if (*na < 0.0) {
 /* jump:2190 */      if (*na == (int32)(*na)) {
        nb[0] = (int32)(*na);
        nb[1] = 1;
 /* jump:2193 */      } else if (*na > -1.0) {
        nb[0] = -(int32)((-*na) * 0x7FFFFFFF);
        nb[1] = 0x7FFFFFFF;
      } else {
        nb[0] = -0x7FFFFFFF;
        nb[1] = (int32)(0x7FFFFFFF / (-*na));
      }
    } else {
 /* jump:2201 */      if (*na == (int32)(*na)) {
        nb[0] = (int32)(*na);
        nb[1] = 1;
 /* jump:2204 */      } else if (*na < 1.0) {
        nb[0] = (int32)((*na) * 0x7FFFFFFF);
        nb[1] = 0x7FFFFFFF;
      } else {
        nb[0] = 0x7FFFFFFF;
        nb[1] = (int32)(0x7FFFFFFF / (*na));
      }
    }
  }
 /* jump:2212 */  if (tif->tif_flags & TIFF_SWAB) {
    TIFFSwabArrayOfLong((uint32 *)m, count * 2);
  }
  o = TIFFWriteDirectoryTagData(tif, ndir, dir, tag, TIFF_SRATIONAL, count,
                                count * 8, &m[0]);
  _TIFFfree(m);
  return (o);
}

static int TIFFWriteDirectoryTagCheckedFloat(TIFF *tif, uint32 *ndir,
                                             TIFFDirEntry *dir, uint16 tag,
                                             float value) {
  float m;
  assert(sizeof(float) == 4);
  m = value;
  TIFFCvtNativeToIEEEFloat(tif, 1, &m);
 /* jump:2228 */  if (tif->tif_flags & TIFF_SWAB) {
    TIFFSwabFloat(&m);
  }
  return (TIFFWriteDirectoryTagData(tif, ndir, dir, tag, TIFF_FLOAT, 1, 4, &m));
}

static int TIFFWriteDirectoryTagCheckedFloatArray(TIFF *tif, uint32 *ndir,
                                                  TIFFDirEntry *dir, uint16 tag,
                                                  uint32 count, float *value) {
  assert(count < 0x40000000);
  assert(sizeof(float) == 4);
  TIFFCvtNativeToIEEEFloat(tif, count, &value);
 /* jump:2240 */  if (tif->tif_flags & TIFF_SWAB) {
    TIFFSwabArrayOfFloat(value, count);
  }
  return (TIFFWriteDirectoryTagData(tif, ndir, dir, tag, TIFF_FLOAT, count,
                                    count * 4, value));
}

static int TIFFWriteDirectoryTagCheckedDouble(TIFF *tif, uint32 *ndir,
                                              TIFFDirEntry *dir, uint16 tag,
                                              double value) {
  double m;
  assert(sizeof(double) == 8);
  m = value;
  TIFFCvtNativeToIEEEDouble(tif, 1, &m);
 /* jump:2254 */  if (tif->tif_flags & TIFF_SWAB) {
    TIFFSwabDouble(&m);
  }
  return (
      TIFFWriteDirectoryTagData(tif, ndir, dir, tag, TIFF_DOUBLE, 1, 8, &m));
}

static int TIFFWriteDirectoryTagCheckedDoubleArray(TIFF *tif, uint32 *ndir,
                                                   TIFFDirEntry *dir,
                                                   uint16 tag, uint32 count,
                                                   double *value) {
  assert(count < 0x20000000);
  assert(sizeof(double) == 8);
  TIFFCvtNativeToIEEEDouble(tif, count, &value);
 /* jump:2268 */  if (tif->tif_flags & TIFF_SWAB) {
    TIFFSwabArrayOfDouble(value, count);
  }
  return (TIFFWriteDirectoryTagData(tif, ndir, dir, tag, TIFF_DOUBLE, count,
                                    count * 8, value));
}

static int TIFFWriteDirectoryTagCheckedIfdArray(TIFF *tif, uint32 *ndir,
                                                TIFFDirEntry *dir, uint16 tag,
                                                uint32 count, uint32 *value) {
  assert(count < 0x40000000);
  assert(sizeof(uint32) == 4);
 /* jump:2280 */  if (tif->tif_flags & TIFF_SWAB) {
    TIFFSwabArrayOfLong(value, count);
  }
  return (TIFFWriteDirectoryTagData(tif, ndir, dir, tag, TIFF_IFD, count,
                                    count * 4, value));
}

static int TIFFWriteDirectoryTagCheckedIfd8Array(TIFF *tif, uint32 *ndir,
                                                 TIFFDirEntry *dir, uint16 tag,
                                                 uint32 count, uint64 *value) {
  assert(count < 0x20000000);
  assert(sizeof(uint64) == 8);
  assert(tif->tif_flags & TIFF_BIGTIFF);
 /* jump:2293 */  if (tif->tif_flags & TIFF_SWAB) {
    TIFFSwabArrayOfLong8(value, count);
  }
  return (TIFFWriteDirectoryTagData(tif, ndir, dir, tag, TIFF_IFD8, count,
                                    count * 8, value));
}

static int TIFFWriteDirectoryTagData(TIFF *tif, uint32 *ndir, TIFFDirEntry *dir,
                                     uint16 tag, uint16 datatype, uint32 count,
                                     uint32 datalength, void *data) {
  static const char module[] = "TIFFWriteDirectoryTagData";
  uint32 m;
  m = 0;
 /* jump:2310 */  while (m < (*ndir)) {
    assert(dir[m].tdir_tag != tag);
 /* jump:2308 */    if (dir[m].tdir_tag > tag) {
      break;
    }
    m++;
  }
 /* jump:2316 */  if (m < (*ndir)) {
    uint32 n;
 /* jump:2315 */    for (n = *ndir; n > m; n--) {
      dir[n] = dir[n - 1];
    }
  }
  dir[m].tdir_tag = tag;
  dir[m].tdir_type = datatype;
  dir[m].tdir_count = count;
  dir[m].tdir_offset = 0;
 /* jump:2323 */  if (datalength <= ((tif->tif_flags & TIFF_BIGTIFF) ? 0x8U : 0x4U)) {
    _TIFFmemcpy(&dir[m].tdir_offset, data, datalength);
  } else {
    uint64 na, nb;
    na = tif->tif_dataoff;
    nb = na + datalength;
 /* jump:2329 */    if (!(tif->tif_flags & TIFF_BIGTIFF)) {
      nb = (uint32)nb;
    }
 /* jump:2334 */    if ((nb < na) || (nb < datalength)) {
      TIFFErrorExt(tif->tif_clientdata, module,
                   "Maximum TIFF file size exceeded");
      return (0);
    }
 /* jump:2338 */    if (!SeekOK(tif, na)) {
      TIFFErrorExt(tif->tif_clientdata, module, "IO error writing tag data");
      return (0);
    }
    assert(datalength < 0x80000000UL);
 /* jump:2343 */    if (!WriteOK(tif, data, (tmsize_t)datalength)) {
      TIFFErrorExt(tif->tif_clientdata, module, "IO error writing tag data");
      return (0);
    }
    tif->tif_dataoff = nb;
 /* jump:2347 */    if (tif->tif_dataoff & 1) {
      tif->tif_dataoff++;
    }
 /* jump:2355 */    if (!(tif->tif_flags & TIFF_BIGTIFF)) {
      uint32 o;
      o = (uint32)na;
 /* jump:2353 */      if (tif->tif_flags & TIFF_SWAB) {
        TIFFSwabLong(&o);
      }
      _TIFFmemcpy(&dir[m].tdir_offset, &o, 4);
    } else {
      dir[m].tdir_offset = na;
 /* jump:2359 */      if (tif->tif_flags & TIFF_SWAB) {
        TIFFSwabLong8(&dir[m].tdir_offset);
      }
    }
  }
  (*ndir)++;
  return (1);
}

/*
 * Link the current directory into the directory chain for the file.
 */
static int TIFFLinkDirectory(TIFF *tif) {
  static const char module[] = "TIFFLinkDirectory";

  tif->tif_diroff = (TIFFSeekFile(tif, 0, SEEK_END) + 1) & ~1;

  /*
   * Handle SubIFDs
   */
 /* jump:2425 */  if (tif->tif_flags & TIFF_INSUBIFD) {
 /* jump:2401 */    if (!(tif->tif_flags & TIFF_BIGTIFF)) {
      uint32 m;
      m = (uint32)tif->tif_diroff;
 /* jump:2383 */      if (tif->tif_flags & TIFF_SWAB) {
        TIFFSwabLong(&m);
      }
      (void)TIFFSeekFile(tif, tif->tif_subifdoff, SEEK_SET);
 /* jump:2389 */      if (!WriteOK(tif, &m, 4)) {
        TIFFErrorExt(tif->tif_clientdata, module,
                     "Error writing SubIFD directory link");
        return (0);
      }
      /*
       * Advance to the next SubIFD or, if this is
       * the last one configured, revert back to the
       * normal directory linkage.
       */
 /* jump:2397 */      if (--tif->tif_nsubifd) {
        tif->tif_subifdoff += 4;
      } else {
        tif->tif_flags &= ~TIFF_INSUBIFD;
      }
      return (1);
    } else {
      uint64 m;
      m = tif->tif_diroff;
 /* jump:2406 */      if (tif->tif_flags & TIFF_SWAB) {
        TIFFSwabLong8(&m);
      }
      (void)TIFFSeekFile(tif, tif->tif_subifdoff, SEEK_SET);
 /* jump:2412 */      if (!WriteOK(tif, &m, 8)) {
        TIFFErrorExt(tif->tif_clientdata, module,
                     "Error writing SubIFD directory link");
        return (0);
      }
      /*
       * Advance to the next SubIFD or, if this is
       * the last one configured, revert back to the
       * normal directory linkage.
       */
 /* jump:2420 */      if (--tif->tif_nsubifd) {
        tif->tif_subifdoff += 8;
      } else {
        tif->tif_flags &= ~TIFF_INSUBIFD;
      }
      return (1);
    }
  }

 /* jump:2483 */  if (!(tif->tif_flags & TIFF_BIGTIFF)) {
    uint32 m;
    uint32 nextdir;
    m = (uint32)(tif->tif_diroff);
 /* jump:2433 */    if (tif->tif_flags & TIFF_SWAB) {
      TIFFSwabLong(&m);
    }
 /* jump:2446 */    if (tif->tif_header.classic.tiff_diroff == 0) {
      /*
       * First directory, overwrite offset in header.
       */
      tif->tif_header.classic.tiff_diroff = (uint32)tif->tif_diroff;
      (void)TIFFSeekFile(tif, 4, SEEK_SET);
 /* jump:2444 */      if (!WriteOK(tif, &m, 4)) {
        TIFFErrorExt(tif->tif_clientdata, tif->tif_name,
                     "Error writing TIFF header");
        return (0);
      }
      return (1);
    }
    /*
     * Not the first directory, search to the last and append.
     */
    nextdir = tif->tif_header.classic.tiff_diroff;
 /* jump:2482 */    while (1) {
      uint16 dircount;
      uint32 nextnextdir;

 /* jump:2459 */      if (!SeekOK(tif, nextdir) || !ReadOK(tif, &dircount, 2)) {
        TIFFErrorExt(tif->tif_clientdata, module,
                     "Error fetching directory count");
        return (0);
      }
 /* jump:2462 */      if (tif->tif_flags & TIFF_SWAB) {
        TIFFSwabShort(&dircount);
      }
      (void)TIFFSeekFile(tif, nextdir + 2 + dircount * 12, SEEK_SET);
 /* jump:2468 */      if (!ReadOK(tif, &nextnextdir, 4)) {
        TIFFErrorExt(tif->tif_clientdata, module,
                     "Error fetching directory link");
        return (0);
      }
 /* jump:2471 */      if (tif->tif_flags & TIFF_SWAB) {
        TIFFSwabLong(&nextnextdir);
      }
 /* jump:2480 */      if (nextnextdir == 0) {
        (void)TIFFSeekFile(tif, nextdir + 2 + dircount * 12, SEEK_SET);
 /* jump:2478 */        if (!WriteOK(tif, &m, 4)) {
          TIFFErrorExt(tif->tif_clientdata, module,
                       "Error writing directory link");
          return (0);
        }
        break;
      }
      nextdir = nextnextdir;
    }
  } else {
    uint64 m;
    uint64 nextdir;
    m = tif->tif_diroff;
 /* jump:2489 */    if (tif->tif_flags & TIFF_SWAB) {
      TIFFSwabLong8(&m);
    }
 /* jump:2502 */    if (tif->tif_header.big.tiff_diroff == 0) {
      /*
       * First directory, overwrite offset in header.
       */
      tif->tif_header.big.tiff_diroff = tif->tif_diroff;
      (void)TIFFSeekFile(tif, 8, SEEK_SET);
 /* jump:2500 */      if (!WriteOK(tif, &m, 8)) {
        TIFFErrorExt(tif->tif_clientdata, tif->tif_name,
                     "Error writing TIFF header");
        return (0);
      }
      return (1);
    }
    /*
     * Not the first directory, search to the last and append.
     */
    nextdir = tif->tif_header.big.tiff_diroff;
 /* jump:2545 */    while (1) {
      uint64 dircount64;
      uint16 dircount;
      uint64 nextnextdir;

 /* jump:2516 */      if (!SeekOK(tif, nextdir) || !ReadOK(tif, &dircount64, 8)) {
        TIFFErrorExt(tif->tif_clientdata, module,
                     "Error fetching directory count");
        return (0);
      }
 /* jump:2519 */      if (tif->tif_flags & TIFF_SWAB) {
        TIFFSwabLong8(&dircount64);
      }
 /* jump:2524 */      if (dircount64 > 0xFFFF) {
        TIFFErrorExt(tif->tif_clientdata, module,
                     "Sanity check on tag count failed, likely corrupt TIFF");
        return (0);
      }
      dircount = (uint16)dircount64;
      (void)TIFFSeekFile(tif, nextdir + 8 + dircount * 20, SEEK_SET);
 /* jump:2531 */      if (!ReadOK(tif, &nextnextdir, 8)) {
        TIFFErrorExt(tif->tif_clientdata, module,
                     "Error fetching directory link");
        return (0);
      }
 /* jump:2534 */      if (tif->tif_flags & TIFF_SWAB) {
        TIFFSwabLong8(&nextnextdir);
      }
 /* jump:2543 */      if (nextnextdir == 0) {
        (void)TIFFSeekFile(tif, nextdir + 8 + dircount * 20, SEEK_SET);
 /* jump:2541 */        if (!WriteOK(tif, &m, 8)) {
          TIFFErrorExt(tif->tif_clientdata, module,
                       "Error writing directory link");
          return (0);
        }
        break;
      }
      nextdir = nextnextdir;
    }
  }
  return (1);
}

/* vim: set ts=8 sts=8 sw=8 noet: */
