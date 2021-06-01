--TEST--
gzcompress()/gzuncompress()
--SKIPIF--
<?php if (!extension_loaded("zlib")) print "skip"; ?>
--FILE--
<?php /* $Id: 002.phpt 242949 2007-09-26 15:44:16Z cvs2svn $ */
$original = str_repeat("hallo php",4096);
$packed=gzcompress($original);
echo strlen($packed)." ".strlen($original)."\n";
$unpacked=gzuncompress($packed);
if (strcmp($original,$unpacked)==0) echo "Strings are equal\n";

/* with explicit compression level, length */
$original = str_repeat("hallo php",4096);
$packed=gzcompress($original, 9);
echo strlen($packed)." ".strlen($original)."\n";
$unpacked=gzuncompress($packed, 40000);
if (strcmp($original,$unpacked)==0) echo "Strings are equal\n";
?>
--EXPECT--
106 36864
Strings are equal
106 36864
Strings are equal
