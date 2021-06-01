--TEST--
BZ2 with files
--SKIPIF--
<?php if (!extension_loaded("bz2")) print "skip"; ?>
--FILE--
<?php // $Id: with_files.phpt 242949 2007-09-26 15:44:16Z cvs2svn $

error_reporting(E_ALL);

$filename = "testfile.bz2";
$str = "This is a test string.\n";
$bz = bzopen($filename, "w");
bzwrite($bz, $str);
bzclose($bz);

$bz = bzopen($filename, "r");
print bzread($bz, 10);
print bzread($bz);
bzclose($bz);
unlink($filename);

--EXPECT--
This is a test string.
