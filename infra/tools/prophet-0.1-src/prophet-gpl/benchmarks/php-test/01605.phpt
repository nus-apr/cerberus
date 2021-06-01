--TEST--
075: Redefining compile-time constants
--FILE--
<?php
namespace foo;
const NULL = 1;

echo NULL;
--EXPECTF--
Fatal error: Cannot redeclare constant 'NULL' in %s.php on line %d
