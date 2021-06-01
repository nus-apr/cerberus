--TEST--
Bug #29566 (foreach/string handling strangeness)
--FILE--
<?php
$var="This is a string";

$dummy="";
unset($dummy);

foreach($var['nosuchkey'] as $v) {
}
?>
===DONE===
--EXPECTF--
Warning: Invalid argument supplied for foreach() in %s.php on line %d
===DONE===
