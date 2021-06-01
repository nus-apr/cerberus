--TEST--
Bug #54262 (Crash when assigning value to a dimension in a non-array)
--FILE--
<?php
$a = '0';
var_dump(isset($a['b']));
$simpleString = preg_match('//', '', $a->a);
$simpleString["wrong"] = "f";
echo "ok\n";
?>
--EXPECTF--
bool(true)

Warning: Attempt to modify property of non-object in %s.php on line 4

Warning: Cannot use a scalar value as an array in %s.php on line 5
ok