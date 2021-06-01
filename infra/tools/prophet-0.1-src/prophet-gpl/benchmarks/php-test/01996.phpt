--TEST--
Bug #8700 (getFromIndex(0) fails)
--SKIPIF--
<?php
/* $Id: bug8700.phpt 260091 2008-05-21 09:27:41Z pajoye $ */
if(!extension_loaded('zip')) die('skip');
?>
--FILE--
<?php
$thisdir = dirname(__FILE__);
$filename = $thisdir . "/bug8009.zip";

$zip = new ZipArchive();

if ($zip->open($filename) === FALSE) {
       exit("cannot open $filename\n");
}
$contents_from_idx = $zip->getFromIndex(0);
$contents_from_name = $zip->getFromName('1.txt');
if ($contents_from_idx != $contents_from_name) {
	echo "failed:";
	var_dump($content_from_idx, $content_from_name);
}

$zip->close();
echo "status: " . $zip->status . "\n";
echo "\n";

--EXPECT--
status: 0
