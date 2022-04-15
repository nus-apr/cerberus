SRC_FILE=experiments/vulnloc/libming/CVE-2016-9264/src/util/listmp3.c
TRANS_FILE=benchmark/vulnloc/libming/CVE-2016-9264/valkyrie/listmp3.c
clang-tidy $SRC_FILE -fix -checks="readability-braces-around-statements"
clang-format -style=LLVM  $SRC_FILE > $TRANS_FILE
cp $TRANS_FILE $SRC_FILE
clang -Xclang -ast-dump=json $SRC_FILE > $TRANS_FILE.ast
tr --delete '\n' <  $TRANS_FILE.ast  >  $TRANS_FILE.ast.single
# check for multi-line if condition / for condition  / while condition
python3 scripts/annotate.py $TRANS_FILE $TRANS_FILE.ast.single
cp formatted.c $TRANS_FILE

