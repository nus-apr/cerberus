--TEST--
Bug #43344.10 (Wrong error message for undefined namespace constant)
--FILE--
<?php
echo namespace\bar."\n";
?>
--EXPECTF--
Fatal error: Undefined constant 'bar' in %s.php on line %d
