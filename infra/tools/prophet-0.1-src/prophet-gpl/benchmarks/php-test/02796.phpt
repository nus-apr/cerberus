--TEST--
zend multibyte (11)
--SKIPIF--
<?php
ini_set("mbstring.script_encoding","SJIS");
if (ini_set("mbstring.script_encoding","SJIS") != "SJIS") {
	die("skip zend-multibyte is not available");
}
?>
--FILE--
<?php
declare(encoding="ISO-8859-15") {
	declare(encoding="ISO-8859-1");
	echo "ok\n";
}
?>
--EXPECTF--
ok
