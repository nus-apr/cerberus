--TEST--
Bug #36010 (Crash when executing SQL statment with lob parameter twice)
--SKIPIF--
<?php if (!extension_loaded('oci8')) die("skip no oci8 extension"); ?>
--FILE--
<?php
	
require dirname(__FILE__).'/connect.inc';

function f($conn)
{
	$sql =  "begin :p_clob := 'lob string'; end;";
	$stid = oci_parse($conn, $sql);
	$clob = oci_new_descriptor($conn, OCI_D_LOB);
	oci_bind_by_name($stid, ":p_clob", $clob, -1, OCI_B_CLOB);
	$r = oci_execute($stid, OCI_DEFAULT);
}

f($c);
f($c);

echo "Done\n";

?>
--EXPECT--
Done
