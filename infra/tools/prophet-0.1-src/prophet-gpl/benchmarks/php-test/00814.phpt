--TEST--
077: Unknown compile-time constants in namespace
--FILE--
<?php

function foo($a = array(namespace\unknown => unknown))
{
}

foo();
--EXPECTF--
Fatal error: Undefined constant 'unknown' in %s.php on line %d
