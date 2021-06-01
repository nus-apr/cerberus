--TEST--
Phar::buildFromIterator() RegexIterator(RecursiveIteratorIterator), SplFileInfo as current
--SKIPIF--
<?php
if (!extension_loaded("phar")) die("skip");
?>
--INI--
phar.require_hash=0
phar.readonly=0
--FILE--
<?php
try {
	chdir(dirname(__FILE__));
	$phar = new Phar(dirname(__FILE__) . '/buildfromiterator.phar');
	$dir = new RecursiveDirectoryIterator('.');
	$iter = new RecursiveIteratorIterator($dir);
	$a = $phar->buildFromIterator(new RegexIterator($iter, '/_\d{3}\.phpt$/'), dirname(__FILE__) . DIRECTORY_SEPARATOR);
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
array(35) {
  ["phar_ctx_001.phpt"]=>
  string(%d) "%s.phpt"
  ["phar_get_supported_signatures_001.phpt"]=>
  string(%d) "%s.phpt"
  ["phar_get_supported_signatures_002.phpt"]=>
  string(%d) "%s.phpt"
  ["phar_oo_001.phpt"]=>
  string(%d) "%s.phpt"
  ["phar_oo_002.phpt"]=>
  string(%d) "%s.phpt"
  ["phar_oo_003.phpt"]=>
  string(%d) "%s.phpt"
  ["phar_oo_004.phpt"]=>
  string(%d) "%s.phpt"
  ["phar_oo_005.phpt"]=>
  string(%d) "%s.phpt"
  ["phar_oo_006.phpt"]=>
  string(%d) "%s.phpt"
  ["phar_oo_007.phpt"]=>
  string(%d) "%s.phpt"
  ["phar_oo_008.phpt"]=>
  string(%d) "%s.phpt"
  ["phar_oo_009.phpt"]=>
  string(%d) "%s.phpt"
  ["phar_oo_010.phpt"]=>
  string(%d) "%s.phpt"
  ["phar_oo_011.phpt"]=>
  string(%d) "%s.phpt"
  ["phar_oo_012.phpt"]=>
  string(%d) "%s.phpt"
  ["phar_oo_compressed_001.phpt"]=>
  string(%d) "%s.phpt"
  ["phar_oo_compressed_002.phpt"]=>
  string(%d) "%s.phpt"
  ["phpinfo_001.phpt"]=>
  string(%d) "%s.phpt"
  ["phpinfo_002.phpt"]=>
  string(%d) "%s.phpt"
  ["phpinfo_003.phpt"]=>
  string(%d) "%s.phpt"
  ["phpinfo_004.phpt"]=>
  string(%d) "%s.phpt"
  ["tar/tar_001.phpt"]=>
  string(%d) "%s.phpt"
  ["tar/tar_002.phpt"]=>
  string(%d) "%s.phpt"
  ["tar/tar_003.phpt"]=>
  string(%d) "%s.phpt"
  ["tar/tar_004.phpt"]=>
  string(%d) "%s.phpt"
  ["zip/corrupt_001.phpt"]=>
  string(%d) "%s.phpt"
  ["zip/corrupt_002.phpt"]=>
  string(%d) "%s.phpt"
  ["zip/corrupt_003.phpt"]=>
  string(%d) "%s.phpt"
  ["zip/corrupt_004.phpt"]=>
  string(%d) "%s.phpt"
  ["zip/corrupt_005.phpt"]=>
  string(%d) "%s.phpt"
  ["zip/corrupt_006.phpt"]=>
  string(%d) "%s.phpt"
  ["zip/corrupt_007.phpt"]=>
  string(%d) "%s.phpt"
  ["zip/corrupt_008.phpt"]=>
  string(%d) "%s.phpt"
  ["zip/corrupt_009.phpt"]=>
  string(%d) "%s.phpt"
  ["zip/corrupt_010.phpt"]=>
  string(%d) "%s.phpt"
}
===DONE===
