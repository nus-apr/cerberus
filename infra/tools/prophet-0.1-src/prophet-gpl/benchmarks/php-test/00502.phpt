--TEST--
ZE2 A static abstract methods
--FILE--
<?php

interface showable
{
	static function show();
}

class pass implements showable
{
	static function show() {
		echo "Call to function show()\n";
	}
}

pass::show();

eval('
class fail
{
	abstract static function func();
}
');

fail::show();

echo "Done\n"; // shouldn't be displayed
?>
--EXPECTF--
Call to function show()

Strict Standards: Static function fail::func() should not be abstract in %s.php(%d) : eval()'d code on line %d

Fatal error: Class fail contains 1 abstract method and must therefore be declared abstract or implement the remaining methods (fail::func) in %s.php(%d) : eval()'d code on line %d
