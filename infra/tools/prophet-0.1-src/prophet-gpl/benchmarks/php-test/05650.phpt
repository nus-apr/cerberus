--TEST--
PECL Bug #10194 (segfault in Instant Client when memory_limit is reached inside the callback) 
--SKIPIF--
<?php if (!extension_loaded('oci8')) die("skip no oci8 extension"); ?>
--INI--
memory_limit=10M
--FILE--
<?php
	
require dirname(__FILE__).'/connect.inc';
require dirname(__FILE__).'/create_table.inc';

$ora_sql = "INSERT INTO
                       ".$schema.$table_name." (clob)
                      VALUES (empty_clob())
                      ";

$statement = oci_parse($c,$ora_sql);
oci_execute($statement);

$ora_sql = "SELECT clob FROM ".$schema.$table_name." FOR UPDATE";
$statement = oci_parse($c,$ora_sql);
oci_execute($statement, OCI_DEFAULT);

$row = oci_fetch_assoc($statement);

$string = str_repeat("test", 32768*4*4);

for ($i = 0; $i < 8; $i++) {
	$row['CLOB']->write($string);
}

oci_commit($c);

$ora_sql = "SELECT clob FROM ".$schema.$table_name."";
$statement = oci_parse($c,$ora_sql);
oci_execute($statement);

$row = oci_fetch_assoc($statement);
var_dump(strlen($row['CLOB']->load())); /* here it should fail */

require dirname(__FILE__).'/drop_table.inc';

echo "Done\n";
?>
--EXPECTF--	
Fatal error: Allowed memory size of 10485760 bytes exhausted%s(tried to allocate %d bytes) in %s on line %d
