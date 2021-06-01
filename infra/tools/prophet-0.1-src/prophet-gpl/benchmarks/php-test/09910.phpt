--TEST--
Phar::buildFromIterator() RegexIterator(DirectoryIterator), SplFileInfo as current
--SKIPIF--
<?php if (!extension_loaded("phar")) die("skip"); ?>
--INI--
phar.readonly=0
--FILE--
<?php
try {
	chdir(dirname(__FILE__));
	$phar = new Phar(dirname(__FILE__) . '/buildfromiterator.phar');
	$a = $phar->buildFromIterator(new RegexIterator(new DirectoryIterator('.'), '/^\d{0,3}\.phpt\\z|^\.\\z|^\.\.\\z/'), dirname(__FILE__) . DIRECTORY_SEPARATOR);
	asort($a);
	var_dump($a);
} catch (Exception $e) {
	var_dump(get_class($e));
	echo $e->getMessage() . "\n";
}
?>
===DONE===
--CLEAN--
<?php 
unlink(dirname(__FILE__) . '/buildfromiterator.phar');
__HALT_COMPILER();
?>
--EXPECTF--
array(33) {
  ["001.phpt"]=>
  string(%d) "%s.phpt"
  ["002.phpt"]=>
  string(%d) "%s.phpt"
  ["003.phpt"]=>
  string(%d) "%s.phpt"
  ["004.phpt"]=>
  string(%d) "%s.phpt"
  ["005.phpt"]=>
  string(%d) "%s.phpt"
  ["006.phpt"]=>
  string(%d) "%s.phpt"
  ["007.phpt"]=>
  string(%d) "%s.phpt"
  ["008.phpt"]=>
  string(%d) "%s.phpt"
  ["009.phpt"]=>
  string(%d) "%s.phpt"
  ["010.phpt"]=>
  string(%d) "%s.phpt"
  ["011.phpt"]=>
  string(%d) "%s.phpt"
  ["012.phpt"]=>
  string(%d) "%s.phpt"
  ["013.phpt"]=>
  string(%d) "%s.phpt"
  ["014.phpt"]=>
  string(%d) "%s.phpt"
  ["015.phpt"]=>
  string(%d) "%s.phpt"
  ["016.phpt"]=>
  string(%d) "%s.phpt"
  ["017.phpt"]=>
  string(%d) "%s.phpt"
  ["018.phpt"]=>
  string(%d) "%s.phpt"
  ["019.phpt"]=>
  string(%d) "%s.phpt"
  ["020.phpt"]=>
  string(%d) "%s.phpt"
  ["021.phpt"]=>
  string(%d) "%s.phpt"
  ["022.phpt"]=>
  string(%d) "%s.phpt"
  ["023.phpt"]=>
  string(%d) "%s.phpt"
  ["024.phpt"]=>
  string(%d) "%s.phpt"
  ["025.phpt"]=>
  string(%d) "%s.phpt"
  ["026.phpt"]=>
  string(%d) "%s.phpt"
  ["027.phpt"]=>
  string(%d) "%s.phpt"
  ["028.phpt"]=>
  string(%d) "%s.phpt"
  ["029.phpt"]=>
  string(%d) "%s.phpt"
  ["030.phpt"]=>
  string(%d) "%s.phpt"
  ["031.phpt"]=>
  string(%d) "%s.phpt"
  ["032.phpt"]=>
  string(%d) "%s.phpt"
  ["033.phpt"]=>
  string(%d) "%s.phpt"
}
===DONE===
