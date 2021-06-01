--TEST--
Bug #43344.6 (Wrong error message for undefined namespace constant)
--FILE--
<?php
namespace Foo;
echo namespace\bar."\n";
?>
--EXPECTF--
Fatal error: Undefined constant 'Foo\bar' in %s.php on line %d
