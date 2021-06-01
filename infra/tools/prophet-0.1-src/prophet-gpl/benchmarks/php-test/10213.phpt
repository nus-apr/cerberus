--TEST--
Phar: create a completely new zip-based phar
--SKIPIF--
<?php if (!extension_loaded("phar")) die("skip"); ?>
--INI--
phar.readonly=1
phar.require_hash=1
--FILE--
<?php

file_put_contents('phar://' . dirname(__FILE__) . '/' . basename(__FILE__, '.php') . '.phar.zip/a.php',
	'brand new!');
include 'phar://' . dirname(__FILE__) . '/' . basename(__FILE__, '.php') . '.phar.zip/a.php';
?>

===DONE===
--CLEAN--
<?php unlink(dirname(__FILE__) . '/' . basename(__FILE__, '.clean.php') . '.phar.zip'); ?>
--EXPECTF--

Warning: file_put_contents(phar://%s.php): failed to open stream: phar error: write operations disabled by the php.ini setting phar.readonly in %s.php on line %d

Warning: include(phar://%s.php): failed to open stream: %s in %s.php on line %d

Warning: include(): Failed opening 'phar://%s.php' for inclusion (include_path='%s') in %s.php on line %d

===DONE===
