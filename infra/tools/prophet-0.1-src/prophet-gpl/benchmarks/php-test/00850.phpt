--TEST--
Heredoc with double quotes syntax but missing second quote
--FILE--
<?php
$test = "foo";
$var = <<<"MYLABEL
test: $test
MYLABEL;
echo $var;
?>
--EXPECTF--
Parse error: %s in %s.php on line %d
