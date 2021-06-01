--TEST--
string offset 002
--FILE--
<?php
$a = "aaa";
$x = array(&$a[1]);
?>
--EXPECTF--
Fatal error: Cannot create references to/from string offsets in %s.php on line 3
