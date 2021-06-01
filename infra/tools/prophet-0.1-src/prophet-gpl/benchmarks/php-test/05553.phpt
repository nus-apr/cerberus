--TEST--
ocilogon() without ORACLE_HOME set (OCIServerAttach() segfaults)
--SKIPIF--
<?php 
if (!extension_loaded('oci8')) die("skip no oci8 extension"); 
ob_start();
phpinfo(INFO_MODULES);
$phpinfo = ob_get_clean();
$ov = preg_match('/Compile-time ORACLE_HOME/', $phpinfo);
if ($ov !== 1) {
	die ("skip Test only valid when OCI8 is built with an ORACLE_HOME");
}
$iv = preg_match('/Oracle .*Version => (10\.2)/', $phpinfo);
if ($iv != 1) {
    die ("skip tests a feature that works only with Oracle 10gR2");
}
?>
--ENV--
ORACLE_HOME=""
--FILE--
<?php

require dirname(__FILE__)."/details.inc";

if (!empty($dbase)) {
	var_dump(ocilogon($user, $password, $dbase));
}
else {
	var_dump(ocilogon($user, $password));
}
	
?>
===DONE===
<?php exit(0); ?>
--EXPECTF--
Warning: ocilogon(): OCIEnvNlsCreate() failed. There is something wrong with your system - please check that ORACLE_HOME and %s are set and point to the right directories in %s on line %d
bool(false)
===DONE===
