--TEST--
Bug #37811 (define not using toString on objects)
--FILE--
<?php

class TestClass
{
	function __toString()
	{
		return "Foo";
	}
}

define("Bar",new TestClass);
var_dump(Bar);
define("Baz",new stdClass);
var_dump(Baz);

?>
===DONE===
--EXPECTF--
string(3) "Foo"

Warning: Constants may only evaluate to scalar values in %s.php on line %d

Notice: Use of undefined constant Baz - assumed 'Baz' in %s.php on line %d
string(3) "Baz"
===DONE===
