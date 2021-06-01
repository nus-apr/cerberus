--TEST--
output buffering - fatalism
--FILE--
<?php
function obh($s)
{
	print_r($s, 1);
}
ob_start("obh");
echo "foo\n";
?>
--EXPECTF--
Fatal error: print_r(): Cannot use output buffering in output buffering display handlers in %s.php on line %d
