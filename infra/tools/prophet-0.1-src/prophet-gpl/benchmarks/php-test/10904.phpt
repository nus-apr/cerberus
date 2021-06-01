--TEST--
XMLReader: libxml2 XML Reader, file data 
--SKIPIF--
<?php if (!extension_loaded("xmlreader")) print "skip"; ?>
--FILE--
<?php 
/* $Id: 002.phpt 204555 2006-01-04 19:44:46Z rrichards $ */
$filename = dirname(__FILE__) . '/_002.xml';
$xmlstring = '<?xml version="1.0" encoding="UTF-8"?>
<books></books>';
file_put_contents($filename, $xmlstring);

$reader = new XMLReader();
if ($reader->open('')) exit();

$reader = new XMLReader();
if (!$reader->open($filename)) {
	$reader->close();
	exit();
}

// Only go through
while ($reader->read()) {
	echo $reader->name."\n";
}
$reader->close();
unlink($filename);
touch($filename);
$reader = new XMLReader();
$reader->open($filename);
$reader->close();
unlink($filename);

?>
===DONE===
--EXPECTF--

Warning: XMLReader::open(): Empty string supplied as input in %s on line %d
books
books
===DONE===
