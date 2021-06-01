--TEST--
077: Unknown compile-time constants in namespace
--FILE--
<?php
namespace foo;

function foo($a = array(\unknown => unknown))
{
}

foo();
--EXPECTF--
Fatal error: Undefined constant 'unknown' in %s.php on line %d
