--TEST--
unset() CV 3 (unset() global variable in included file)
--FILE--
<?php
$x = "ok\n";
echo $x;
include "unset.inc";
echo $x;
?>
--EXPECTF--
ok

Notice: Undefined variable: x in %s.php on line %d
