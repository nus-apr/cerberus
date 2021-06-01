--TEST--
oci_bind_array_by_name() and invalid values 1 
--SKIPIF--
<?php if (!extension_loaded('oci8')) die("skip no oci8 extension"); ?>
--FILE--
<?php

require dirname(__FILE__).'/connect.inc';

$drop = "DROP table bind_test";
$statement = oci_parse($c, $drop);
@oci_execute($statement);

$create = "CREATE table bind_test(name DATE)";
$statement = oci_parse($c, $create);
oci_execute($statement);

$create_pkg = "
CREATE OR REPLACE PACKAGE ARRAYBINDPKG1 AS 
  TYPE ARRTYPE IS TABLE OF DATE INDEX BY BINARY_INTEGER; 
  PROCEDURE iobind(c1 IN OUT ARRTYPE); 
END ARRAYBINDPKG1;";
$statement = oci_parse($c, $create_pkg);
oci_execute($statement);

$create_pkg_body = "
CREATE OR REPLACE PACKAGE BODY ARRAYBINDPKG1 AS 
  CURSOR CUR IS SELECT name FROM bind_test;
  PROCEDURE iobind(c1 IN OUT ARRTYPE) IS
    BEGIN
    FOR i IN 1..5 LOOP
      INSERT INTO bind_test VALUES (c1(i));
    END LOOP;
    IF NOT CUR%ISOPEN THEN
      OPEN CUR;
    END IF;
    FOR i IN REVERSE 1..5 LOOP
      FETCH CUR INTO c1(i);
      IF CUR%NOTFOUND THEN
        CLOSE CUR;
        EXIT;
      END IF;
    END LOOP;
  END iobind;
END ARRAYBINDPKG1;";
$statement = oci_parse($c, $create_pkg_body);
oci_execute($statement);

$statement = oci_parse($c, "BEGIN ARRAYBINDPKG1.iobind(:c1); END;");

$array = "";

oci_bind_array_by_name($statement, ":c1", $array, 5, 5, SQLT_ODT);

oci_execute($statement);

var_dump($array);

echo "Done\n";
?>
--EXPECTF--	
Warning: oci_bind_array_by_name(): OCI-21560: argument 3 is null, invalid, or out of range in %s on line %d

Warning: oci_execute(): ORA-01008: not all variables bound in %s on line %d
array(1) {
  [0]=>
  string(0) ""
}
Done
