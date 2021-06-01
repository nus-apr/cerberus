--TEST--
XMLReader: libxml2 XML Reader, string data 
--SKIPIF--
<?php if (!extension_loaded("xmlreader")) print "skip"; ?>
--FILE--
<?php 
/* $Id: 001.phpt 203342 2005-12-21 03:58:59Z pajoye $ */

$xmlstring = '<?xml version="1.0" encoding="UTF-8"?>
<books></books>';

$reader = new XMLReader();
$reader->XML($xmlstring);

// Only go through
while ($reader->read()) {
	echo $reader->name."\n";
}
$xmlstring = '';
$reader = new XMLReader();
$reader->XML($xmlstring);
?>
===DONE===
--EXPECTF--
books
books

Warning: XMLReader::XML(): Empty string supplied as input in %s on line %d
===DONE===
