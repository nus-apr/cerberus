--TEST--
Bug #47109 (Memory leak on $a->{"a"."b"} when $a is not an object)
--FILE--
<?php
$a->{"a"."b"};
?>
--EXPECTF--
Notice: Undefined variable: a in %s.php on line 2

Notice: Trying to get property of non-object in %s.php on line 2

