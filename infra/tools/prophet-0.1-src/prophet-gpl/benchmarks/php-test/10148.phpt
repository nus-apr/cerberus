--TEST--
Phar::buildFromIterator() iterator, SplFileInfo as current zip-based
--SKIPIF--
<?php if (!extension_loaded("phar")) die("skip"); ?>
--INI--
phar.readonly=0
--FILE--
<?php
try {
	chdir(dirname(__FILE__));
	$phar = new Phar(dirname(__FILE__) . '/buildfromiterator.phar.zip');
	$a = $phar->buildFromIterator(new RegexIterator(new DirectoryIterator('.'), '/^frontcontroller\d{0,2}\.phar\.phpt\\z|^\.\\z|^\.\.\\z/'), dirname(__FILE__) . DIRECTORY_SEPARATOR);
	asort($a);
	var_dump($a);
	var_dump($phar->isFileFormat(Phar::ZIP));
} catch (Exception $e) {
	var_dump(get_class($e));
	echo $e->getMessage() . "\n";
}
?>
===DONE===
--CLEAN--
<?php 
unlink(dirname(__FILE__) . '/buildfromiterator.phar.zip');
__HALT_COMPILER();
?>
--EXPECTF--
array(21) {
  ["frontcontroller1.phar.phpt"]=>
  string(%d) "%s.phpt"
  ["frontcontroller10.phar.phpt"]=>
  string(%d) "%s.phpt"
  ["frontcontroller11.phar.phpt"]=>
  string(%d) "%s.phpt"
  ["frontcontroller12.phar.phpt"]=>
  string(%d) "%s.phpt"
  ["frontcontroller13.phar.phpt"]=>
  string(%d) "%s.phpt"
  ["frontcontroller14.phar.phpt"]=>
  string(%d) "%s.phpt"
  ["frontcontroller15.phar.phpt"]=>
  string(%d) "%s.phpt"
  ["frontcontroller16.phar.phpt"]=>
  string(%d) "%s.phpt"
  ["frontcontroller17.phar.phpt"]=>
  string(%d) "%s.phpt"
  ["frontcontroller18.phar.phpt"]=>
  string(%d) "%s.phpt"
  ["frontcontroller19.phar.phpt"]=>
  string(%d) "%s.phpt"
  ["frontcontroller2.phar.phpt"]=>
  string(%d) "%s.phpt"
  ["frontcontroller20.phar.phpt"]=>
  string(%d) "%s.phpt"
  ["frontcontroller21.phar.phpt"]=>
  string(%d) "%s.phpt"
  ["frontcontroller3.phar.phpt"]=>
  string(%d) "%s.phpt"
  ["frontcontroller4.phar.phpt"]=>
  string(%d) "%s.phpt"
  ["frontcontroller5.phar.phpt"]=>
  string(%d) "%s.phpt"
  ["frontcontroller6.phar.phpt"]=>
  string(%d) "%s.phpt"
  ["frontcontroller7.phar.phpt"]=>
  string(%d) "%s.phpt"
  ["frontcontroller8.phar.phpt"]=>
  string(%d) "%s.phpt"
  ["frontcontroller9.phar.phpt"]=>
  string(%d) "%s.phpt"
}
bool(true)
===DONE===
