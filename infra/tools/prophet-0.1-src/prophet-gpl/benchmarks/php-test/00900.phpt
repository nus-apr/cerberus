--TEST--
Bug #36303 (foreach on error_zval produces segfault)
--FILE--
<?php
$x="test";
foreach($x->a->b as &$v) {
}
echo "ok\n";
?>
--EXPECTF--
Warning: Attempt to modify property of non-object in %s.php on line 3

Warning: Invalid argument supplied for foreach() in %s.php on line 3
ok
