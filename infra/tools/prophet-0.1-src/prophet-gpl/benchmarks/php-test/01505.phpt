--TEST--
059: Constant arrays
--FILE--
<?php
const C = array();
--EXPECTF--
Fatal error: Arrays are not allowed as constants in %s.php on line 2

