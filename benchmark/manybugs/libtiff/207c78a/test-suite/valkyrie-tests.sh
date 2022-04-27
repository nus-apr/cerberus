#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
TEST_ID=$1
cd $script_dir/test

case "$TEST_ID" in
    1)   ./ascii_tag $PATCH_ID ;;
    2)   ./long_tag $PATCH_ID ;;
    3)   ./short_tag $PATCH_ID ;;
    4)   ./strip_rw $PATCH_ID ;;
    5)   ./rewrite $PATCH_ID  ;;
    6)   ./bmp2tiff_palette.sh;;
    7)   ./bmp2tiff_rgb.sh;;
    8)   ./gif2tiff.sh;;
    9)   ./ppm2tiff_pbm.sh;;
    10)   ./ppm2tiff_pgm.sh;;
    11)   ./ppm2tiff_ppm.sh;;
    12)   ./tiffcp-g3.sh;;
    13)   ./tiffcp-g3-1d.sh;;
    14)   ./tiffcp-g3-1d-fill.sh;;
    15)   ./tiffcp-g3-2d.sh;;
    16)   ./tiffcp-g3-2d-fill.sh;;
    17)   ./tiffcp-g4.sh;;
    18)   ./tiffcp-logluv.sh;;
    19)   ./tiffcp-thumbnail.sh;;
    20)   ./tiffdump.sh;;
    21)   ./tiffinfo.sh;;
    22)   ./tiffcp-split.sh;;
    23)   ./tiffcp-split-join.sh;;
    24)   ./tiff2ps-PS1.sh;;
    25)   ./tiff2ps-PS2.sh;;
    26)   ./tiff2ps-PS3.sh;;
    27)   ./tiff2ps-EPS1.sh;;
    28)   ./tiff2pdf.sh;;
    29)   ./tiffcrop-doubleflip-logluv-3c-16b.sh;;
    30)   ./tiffcrop-doubleflip-minisblack-1c-16b.sh;;
    31)   ./tiffcrop-doubleflip-minisblack-1c-8b.sh;;
    32)   ./tiffcrop-doubleflip-minisblack-2c-8b-alpha.sh;;
    33)   ./tiffcrop-doubleflip-miniswhite-1c-1b.sh;;
    34)   ./tiffcrop-doubleflip-palette-1c-1b.sh;;
    35)   ./tiffcrop-doubleflip-palette-1c-4b.sh;;
    36)   ./tiffcrop-doubleflip-palette-1c-8b.sh;;
    37)   ./tiffcrop-doubleflip-rgb-3c-16b.sh;;
    38)   ./tiffcrop-doubleflip-rgb-3c-8b.sh;;
    39)   ./tiffcrop-extract-logluv-3c-16b.sh;;
    40)   ./tiffcrop-extract-minisblack-1c-16b.sh;;
    41)   ./tiffcrop-extract-minisblack-1c-8b.sh;;
    42)   ./tiffcrop-extract-minisblack-2c-8b-alpha.sh;;
    43)   ./tiffcrop-extract-miniswhite-1c-1b.sh;;
    44)   ./tiffcrop-extract-palette-1c-1b.sh;;
    45)   ./tiffcrop-extract-palette-1c-4b.sh;;
    46)   ./tiffcrop-extract-palette-1c-8b.sh;;
    47)   ./tiffcrop-extract-rgb-3c-16b.sh;;
    48)   ./tiffcrop-extract-rgb-3c-8b.sh;;
    49)   ./tiffcrop-extractz14-logluv-3c-16b.sh;;
    50)   ./tiffcrop-extractz14-minisblack-1c-16b.sh;;
    51)   ./tiffcrop-extractz14-minisblack-1c-8b.sh;;
    52)   ./tiffcrop-extractz14-minisblack-2c-8b-alpha.sh;;
    53)   ./tiffcrop-extractz14-miniswhite-1c-1b.sh;;
    54)   ./tiffcrop-extractz14-palette-1c-1b.sh;;
    55)   ./tiffcrop-extractz14-palette-1c-4b.sh;;
    56)   ./tiffcrop-extractz14-palette-1c-8b.sh;;
    57)   ./tiffcrop-extractz14-rgb-3c-16b.sh;;
    58)   ./tiffcrop-extractz14-rgb-3c-8b.sh;;
    59)   ./tiffcrop-R90-logluv-3c-16b.sh;;
    60)   ./tiffcrop-R90-minisblack-1c-16b.sh;;
    61)   ./tiffcrop-R90-minisblack-1c-8b.sh;;
    62)   ./tiffcrop-R90-minisblack-2c-8b-alpha.sh;;
    63)   ./tiffcrop-R90-miniswhite-1c-1b.sh;;
    64)   ./tiffcrop-R90-palette-1c-1b.sh;;
    65)   ./tiffcrop-R90-palette-1c-4b.sh;;
    66)   ./tiffcrop-R90-palette-1c-8b.sh;;
    67)   ./tiffcrop-R90-rgb-3c-16b.sh;;
    68)   ./tiffcrop-R90-rgb-3c-8b.sh;;
    69)   ./tiff2rgba-logluv-3c-16b.sh;;
    70)   ./tiff2rgba-minisblack-1c-16b.sh;;
    71)   ./tiff2rgba-minisblack-1c-8b.sh;;
    72)   ./tiff2rgba-minisblack-2c-8b-alpha.sh;;
    73)   ./tiff2rgba-miniswhite-1c-1b.sh;;
    74)   ./tiff2rgba-palette-1c-1b.sh;;
    75)   ./tiff2rgba-palette-1c-4b.sh;;
    76)   ./tiff2rgba-palette-1c-8b.sh;;
    77)   ./tiff2rgba-rgb-3c-16b.sh;;
    78)   ./tiff2rgba-rgb-3c-8b.sh;;
esac

ret=$?
rm $PATCH_ID-o-*
exit $ret;

