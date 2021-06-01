--TEST--
ZE2 method inheritance without interfaces
--FILE--
<?php

class A
{
	function f() {}
}

class B extends A
{
	function f($x) {}
}

?>
===DONE===
--EXPECTF--

Strict Standards: Declaration of B::f() should be compatible with that of A::f() in %s.php on line %d
===DONE===
