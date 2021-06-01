--TEST--
Bug #43344.3 (Wrong error message for undefined namespace constant)
--FILE--
<?php
namespace Foo;
function f($a=Foo::bar) {
	return $a;
}
echo f()."\n";
?>
--EXPECTF--
Fatal error: Class 'Foo\Foo' not found in %s.php on line %d
