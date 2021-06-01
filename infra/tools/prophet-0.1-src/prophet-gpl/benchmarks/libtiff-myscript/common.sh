# Common code fragment for tests
#
srcdir=${srcdir:-.}
BUILDDIR=`pwd`
SRCDIR=`dirname $0`
SRCDIR=`cd $SRCDIR && pwd`
TOPSRCDIR=`cd $srcdir/.. && pwd`
TOOLS=`cd ../tools && pwd`
IMAGES="${SRCDIR}/images"

# Aliases for built tools
BMP2TIFF=${TOOLS}/bmp2tiff
FAX2PS=${TOOLS}/fax2ps
FAX2TIFF=${TOOLS}/fax2tiff
GIF2TIFF=${TOOLS}/gif2tiff
PAL2RGB=${TOOLS}/pal2rgb
PPM2TIFF=${TOOLS}/ppm2tiff
RAS2TIFF=${TOOLS}/ras2tiff
RAW2TIFF=${TOOLS}/raw2tiff
RGB2YCBCR=${TOOLS}/rgb2ycbcr
THUMBNAIL=${TOOLS}/thumbnail
TIFF2BW=${TOOLS}/tiff2bw
TIFF2PDF=${TOOLS}/tiff2pdf
TIFF2PS=${TOOLS}/tiff2ps
TIFF2RGBA=${TOOLS}/tiff2rgba
TIFFCMP=${TOOLS}/tiffcmp
TIFFCP=${TOOLS}/tiffcp
TIFFCROP=${TOOLS}/tiffcrop
TIFFDITHER=${TOOLS}/tiffdither
TIFFDUMP=${TOOLS}/tiffdump
TIFFINFO=${TOOLS}/tiffinfo
TIFFMEDIAN=${TOOLS}/tiffmedian
TIFFSET=${TOOLS}/tiffset
TIFFSPLIT=${TOOLS}/tiffsplit

# Aliases for input test files
IMG_MINISBLACK_1C_16B=${IMAGES}/minisblack-1c-16b.tiff
IMG_MINISBLACK_1C_8B=${IMAGES}/minisblack-1c-8b.tiff
IMG_MINISWHITE_1C_1B=${IMAGES}/miniswhite-1c-1b.tiff
IMG_PALETTE_1C_1B=${IMAGES}/palette-1c-1b.tiff
IMG_PALETTE_1C_4B=${IMAGES}/palette-1c-4b.tiff
IMG_PALETTE_1C_8B=${IMAGES}/palette-1c-8b.tiff
IMG_RGB_3C_16B=${IMAGES}/rgb-3c-16b.tiff
IMG_RGB_3C_8B=${IMAGES}/rgb-3c-8b.tiff
IMG_MINISBLACK_2C_8B_ALPHA=${IMAGES}/minisblack-2c-8b-alpha.tiff

IMG_PALETTE_1C_8B_BMP=${IMAGES}/palette-1c-8b.bmp
IMG_RGB_3C_8B_BMP=${IMAGES}/rgb-3c-8b.bmp

IMG_PALETTE_1C_8B_GIF=${IMAGES}/palette-1c-8b.gif

IMG_MINISWHITE_1C_1B_PBM=${IMAGES}/miniswhite-1c-1b.pbm
IMG_MINISBLACK_1C_8B_PGM=${IMAGES}/minisblack-1c-8b.pgm
IMG_RGB_3C_8B_PPM=${IMAGES}/rgb-3c-8b.ppm

# All uncompressed image files
IMG_UNCOMPRESSED="${IMG_MINISBLACK_1C_16B} ${IMG_MINISBLACK_1C_8B} ${IMG_MINISWHITE_1C_1B} ${IMG_PALETTE_1C_1B} ${IMG_PALETTE_1C_4B} ${IMG_PALETTE_1C_4B} ${IMG_PALETTE_1C_8B} ${IMG_RGB_3C_8B}"

#
# Test a simple convert-like command.
#
# f_test_convert command infile outfile
f_test_convert ()
{ 
  command=$1
  infile=$2
  outfile=$3
  rm -f $outfile
  echo "$MEMCHECK $command $infile $outfile"
  eval $MEMCHECK $command $infile $outfile
  status=$?
  if [ "$GENEXPOUT" -eq "1" ]; then
      outfs=$(eval echo "${outfile} ${outfile}*.tif")
      echo $outfs
      for outf in $outfs
      do
          if [ -f $outf ]; then
              rm ${outf}.exp
              rm ${outf}.exp.tol
              mv $outf ${outf}.exp
          fi
      done
      sleep 1
      $command $infile $outfile
      for outf in $outfs
      do
          if [ -f $outf ]; then
              diff $outf ${outf}.exp
              diffstatus=$?
              if [ $diffstatus != 0 ]; then
                  xxd $outf > 1.tmp
                  xxd ${outf}.exp > 2.tmp
                  diff 1.tmp 2.tmp > ${outf}.exp.tol
                  rm -rf 1.tmp 2.tmp
              fi
          fi
      done
  fi
  if [ $status != 0 ] ; then
    echo "Returned failed status $status!"
    echo "Output (if any) is in \"${outfile}\"."
    exit $status
  fi
  if [ "$CMPEXPOUT" -eq "1" ]; then
      outfs=$(eval echo "${outfile} ${outfile}*.tif")
      echo $outf
      for outf in $outfs
      do
          if [ -f $outf ]; then
              if file --mime-type "$outf" | grep postscript$; then
                  tail -n+5 $outf > 1.tmp
                  tail -n+5 ${outf}.exp > 2.tmp
                  diff 1.tmp 2.tmp
                  diffstatus=$?
                  rm -rf 1.tmp 2.tmp
              else 
                  xxd $outf > 1.tmp
                  xxd ${outf}.exp > 2.tmp
                  diff 1.tmp 2.tmp > 3.tmp
                  $SRCDIR/smart-diff.py 3.tmp ${outf}.exp.tol
                  diffstatus=$?
                  rm -rf 1.tmp 2.tmp 3.tmp
              fi
              if [ $diffstatus != 0 ]; then
                  echo "Different output file!"
                  echo "Output (if any) is in \"${outfile}\"."
                  exit $diffstatus
              fi
          fi
      done
      expfs=$(eval echo "${outfile}*.exp")
      echo $expfs
      for expf in $expfs
      do
          orif=${expf%.*}
          if [ ! -f $orif ]; then
              echo "Missing \"${orif}\"."
              exit 1
          fi
      done
  fi
}

#
# Test a simple command which sends output to stdout
#
# f_test_stdout command infile outfile
f_test_stdout ()
{ 
  command=$1
  infile=$2
  outfile=$3
  rm -f $outfile
  echo "$MEMCHECK $command $infile > $outfile"
  eval $MEMCHECK $command $infile > $outfile
  status=$?
  if [ "$GENEXPOUT" -eq "1" ]; then
      outfs=$(eval echo "${outfile} ${outfile}*.tif")
      echo $outfs
      for outf in $outfs
      do
          if [ -f $outf ]; then
              rm ${outf}.exp
              rm ${outf}.exp.tol
              mv $outf ${outf}.exp
          fi
      done
      sleep 1
      $command $infile > $outfile
      for outf in $outfs
      do
          if [ -f $outf ]; then
              diff $outf ${outf}.exp
              diffstatus=$?
              if [ $diffstatus != 0 ]; then
                  xxd $outf > 1.tmp
                  xxd ${outf}.exp > 2.tmp
                  diff 1.tmp 2.tmp > ${outf}.exp.tol
                  rm -rf 1.tmp 2.tmp
              fi
          fi
      done
  fi
#  if [ "$GENEXPOUT" -eq "1" ]; then
#      rm ${outfile}.exp
#      rm ${outfile}.exp.tol
#      $command $infile > ${outfile}.exp
#      diff ${outfile} ${outfile}.exp
#      diffstatus=$?
#      if [ $diffstatus != 0 ]; then
#          xxd $outfile > 1.tmp
#          xxd ${outfile}.exp > 2.tmp
#          diff 1.tmp 2.tmp > ${outfile}.exp.tol
#          rm 1.tmp
#          rm 2.tmp
#      fi
#  fi
  if [ $status != 0 ] ; then
    echo "Returned failed status $status!"
    echo "Output (if any) is in \"${outfile}\"."
    exit $status
  fi
  if [ "$CMPEXPOUT" -eq "1" ]; then
      outfs=$(eval echo "${outfile} ${outfile}*.tif")
      echo $outfs
      for outf in $outfs
      do
          if [ -f $outf ]; then
              if file --mime-type "$outf" | grep postscript$; then
                  tail -n+5 $outf > 1.tmp
                  tail -n+5 ${outf}.exp > 2.tmp
                  diff 1.tmp 2.tmp
                  diffstatus=$?
                  rm -rf 1.tmp 2.tmp
              else 
                  xxd $outf > 1.tmp
                  xxd ${outf}.exp > 2.tmp
                  diff 1.tmp 2.tmp > 3.tmp
                  $SRCDIR/smart-diff.py 3.tmp ${outf}.exp.tol
                  diffstatus=$?
                  rm -rf 1.tmp 2.tmp 3.tmp
              fi
              if [ $diffstatus != 0 ]; then
                  echo "Different output file!"
                  echo "Output (if any) is in \"${outfile}\"."
                  exit $diffstatus
              fi
          fi
      done
      expfs=$(eval echo "${outfile}*.exp")
      echo $expfs
      for expf in $expfs
      do
          orif=${expf%.*}
          if [ ! -f $orif ]; then
              echo "Missing \"${orif}\"."
              exit 1
          fi
      done
  fi
}

#
# Execute a simple command (e.g. tiffinfo) with one input file
#
# f_test_exec command infile
f_test_reader ()
{ 
  command=$1
  infile=$2
  echo "$MEMCHECK $command $infile"
  eval $MEMCHECK $command $infile
  status=$?
  if [ $status != 0 ] ; then
    echo "Returned failed status $status!"
    exit $status
  fi
}

#
# Execute tiffinfo on a specified file to validate it
#
# f_tiffinfo_validate infile
f_tiffinfo_validate ()
{
    f_test_reader "$TIFFINFO -D" $1
}

if test "$VERBOSE" = TRUE
then
  set -x
fi

