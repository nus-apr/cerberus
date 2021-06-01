--TEST--
Phar: bug #46032: PharData::__construct wrong memory read
--SKIPIF--
<?php if (!extension_loaded("phar")) die("skip"); ?>
<?php if (getenv('SKIP_SLOW_TESTS')) die('skip'); ?>
--FILE--
<?php

$a = dirname(__FILE__) .'/mytest';

try {
	new phar($a);
} catch (exception $e) { }

var_dump($a);

try {
	new phar($a);
} catch (exception $e) { }

var_dump($a);

new phardata('0000000000000000000');
?>
===DONE===
--EXPECTF--
%string|unicode%(%d) "%smytest"
%string|unicode%(%d) "%smytest"

Fatal error: Uncaught exception 'UnexpectedValueException' with message 'Cannot create phar '0000000000000000000', file extension (or combination) not recognised or the directory does not exist' in %s.php:%d
Stack trace:
#0 %s.php(%d): PharData->__construct('000000000000000...')
#1 {main}
  thrown in %s.php on line %d
