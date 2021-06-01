--TEST--
SPL: Bug #48361 SpleFileInfo::getPathName should return the dirname's path
--FILE--
<?php
$info = new SplFileInfo(__FILE__);
var_dump($info->getRealPath());
var_dump($info->getPathInfo()->getRealPath());
?>
===DONE===
--EXPECTF--
string(%d) "%s.php"
string(%d) "%stests"
===DONE===

