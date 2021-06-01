--TEST--
Bug #43344.2 (Wrong error message for undefined namespace constant)
--FILE--
<?php
namespace Foo;
echo Foo::bar."\n";
?>
--EXPECTF--
Fatal error: Class 'Foo\Foo' not found in %s.php on line %d
