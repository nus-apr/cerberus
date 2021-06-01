--TEST--
oci_connect() without ORACLE_HOME set (OCIServerAttach() segfaults)
--SKIPIF--
<?php 
if (!extension_loaded('oci8')) die("skip no oci8 extension"); 
ob_start();
phpinfo(INFO_MODULES);
$phpinfo = ob_get_clean();
$ov = preg_match('/Compile-time ORACLE_HOME/', $phpinfo);
if ($ov != 1) {
	die ("skip Test only valid when OCI8 is built with an ORACLE_HOME");
}
$iv = preg_match('/Oracle .*Version => (11\.2|12)/', $phpinfo);
if ($iv != 1) {
        die ("skip tests a feature that works only with Oracle 11gR2 or greater version of client");
}
?>
--ENV--
ORACLE_HOME=""
--FILE--
<?php

require dirname(__FILE__)."/details.inc";

if (!empty($dbase)) {
	var_dump(oci_connect($user, $password, $dbase));
}
else {
	var_dump(oci_connect($user, $password));
}
	
?>
===DONE===
<?php exit(0); ?>
--EXPECTF--
Warning: oci_connect(): OCIEnvNlsCreate() failed. There is something wrong with your system - please check that ORACLE_HOME and %s are set and point to the right directories in %s on line %d

Warning: oci_connect(): Error while trying to retrieve text for error ORA-01804
 in %s on line %d
bool(false)
===DONE===
