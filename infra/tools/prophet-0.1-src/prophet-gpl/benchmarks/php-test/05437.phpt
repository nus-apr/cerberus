--TEST--
Test OCI_NO_AUTO_COMMIT constant
--SKIPIF--
<?php if (!extension_loaded('oci8')) die("skip no oci8 extension"); ?>
--FILE--
<?php

require(dirname(__FILE__)."/connect.inc");
require(dirname(__FILE__).'/create_table.inc');

$insert_sql = "insert into ".$schema.$table_name." (id, value) values (1,1)";

if (!($s = oci_parse($c, $insert_sql))) {
	die("oci_parse(insert) failed!\n");
}

/* check with OCI_NO_AUTO_COMMIT mode  */
for ($i = 0; $i<3; $i++) {
	if (!oci_execute($s, OCI_NO_AUTO_COMMIT)) {
		die("oci_execute(insert) failed!\n");
	}
}

for ($i = 0; $i<3; $i++) {
	if (!oci_execute($s, OCI_DEFAULT)) {
		die("oci_execute(insert) failed!\n");
	}
}


var_dump(oci_rollback($c));

$select_sql = "select * from ".$schema.$table_name."";

if (!($select = oci_parse($c, $select_sql))) {
	die("oci_parse(select) failed!\n");
}

/* oci_fetch_all */
if (!oci_execute($select)) {
	die("oci_execute(select) failed!\n");
}
var_dump(oci_fetch_all($select, $all));
var_dump($all);

/* ocifetchstatement */
if (!oci_execute($s)) {
	die("oci_execute(select) failed!\n");
}

$insert_sql = "insert into ".$schema.$table_name." (id, value) values (1,1)";

if (!($s = oci_parse($c, $insert_sql))) {
    die("oci_parse(insert) failed!\n");
}

for ($i = 0; $i<3; $i++) {
    if (!oci_execute($s, OCI_DEFAULT)) {
        die("oci_execute(insert) failed!\n");
    }
}

var_dump(oci_commit($c));

/* oci_fetch_all */
if (!oci_execute($select)) {
	die("oci_execute(select) failed!\n");
}
var_dump(oci_fetch_all($select, $all));
var_dump($all);


require(dirname(__FILE__).'/drop_table.inc');
	
echo "Done\n";
?>
--EXPECTF--
bool(true)
int(0)
array(5) {
  [%u|b%"ID"]=>
  array(0) {
  }
  [%u|b%"VALUE"]=>
  array(0) {
  }
  [%u|b%"BLOB"]=>
  array(0) {
  }
  [%u|b%"CLOB"]=>
  array(0) {
  }
  [%u|b%"STRING"]=>
  array(0) {
  }
}
bool(true)
int(4)
array(5) {
  [%u|b%"ID"]=>
  array(4) {
    [0]=>
    %string|unicode%(1) "1"
    [1]=>
    %string|unicode%(1) "1"
    [2]=>
    %string|unicode%(1) "1"
    [3]=>
    %string|unicode%(1) "1"
  }
  [%u|b%"VALUE"]=>
  array(4) {
    [0]=>
    %string|unicode%(1) "1"
    [1]=>
    %string|unicode%(1) "1"
    [2]=>
    %string|unicode%(1) "1"
    [3]=>
    %string|unicode%(1) "1"
  }
  [%u|b%"BLOB"]=>
  array(4) {
    [0]=>
    NULL
    [1]=>
    NULL
    [2]=>
    NULL
    [3]=>
    NULL
  }
  [%u|b%"CLOB"]=>
  array(4) {
    [0]=>
    NULL
    [1]=>
    NULL
    [2]=>
    NULL
    [3]=>
    NULL
  }
  [%u|b%"STRING"]=>
  array(4) {
    [0]=>
    NULL
    [1]=>
    NULL
    [2]=>
    NULL
    [3]=>
    NULL
  }
}
Done
