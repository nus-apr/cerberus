--TEST--
Prefetch with Nested cursors with INI setting.
--INI--
oci8.default_prefetch=5
--SKIPIF--
<?php if (!extension_loaded('oci8')) die("skip no oci8 extension");
if (!extension_loaded('oci8')) die("skip no oci8 extension");
require(dirname(__FILE__)."/connect.inc");
ob_start();
phpinfo(INFO_MODULES);
$phpinfo = ob_get_clean();
$iv = preg_match('/Oracle .*Version => (11\.2|12\.)/', $phpinfo);
if ($iv == 1) {
    $sv = oci_server_version($c);
    $sv = preg_match('/Release (11\.2|12\.)/', $sv, $matches);
    if ($sv != 1) {
        die ("skip expected output only valid when using Oracle 11.2 or greater server");
    }
}
else {
    die ("skip expected output only valid when using Oracle 11.2 or greater client");
}

?>
--FILE--
<?php
require dirname(__FILE__)."/connect.inc";

//Create tables here
$stmtarray = array(
    "drop table nescurtest",
    "create table nescurtest(c1 varchar2(10))"
);

foreach($stmtarray as $stmt) {
    $s = oci_parse($c,$stmt);
    $r = @oci_execute($s);
    if (!$r) {
        $msg = oci_error($s);
		if ($msg['code'] !=942) {
            echo $msg['message'],"\n";
		}
    }
}
// Insert 500 rows into the table.
$insert_sql = "INSERT INTO nescurtest (c1) VALUES (:c1)";
if (!($s = oci_parse($c, $insert_sql))) {
    die("oci_parse(insert) failed!\n");
}

for ($i = 0; $i<=500; $i++) {
    $val2 = 'test'.$i;
    oci_bind_by_name($s,':c1',$val2);
    if (!oci_execute($s)) {
        die("oci_execute(insert) failed!\n");
    }
}

echo"-----------------------------------------------\n";
echo "Test with Nested Cursors\n";
echo"-----------------------------------------------\n";
$cur1 = oci_new_cursor($c);
$sqlstmt = "select cursor(select * from nescurtest) curs1 from dual";
$s = oci_parse($c,$sqlstmt);
oci_execute($s);
$data = oci_fetch_array($s);
oci_execute($data['CURS1']);

// Calculate round-trips 
$initial_rt = print_roundtrips($c);
for ($i = 0;$i<10;$i++) {
    echo "Fetch Row using Nested cursor Query\n";
    var_dump(oci_fetch_row($data['CURS1']));
}

$cnt = (print_roundtrips($c) - $initial_rt);
echo "Number of roundtrips made with prefetch count 5 for 10 rows is  $cnt\n";

function  print_roundtrips($c) {
    $sql_stmt = "select value from v\$mystat a,v\$statname c where
         a.statistic#=c.statistic# and c.name='SQL*Net roundtrips to/from client'";
    $s = oci_parse($c,$sql_stmt);
    oci_define_by_name($s,"VALUE",$value);
    oci_execute($s);
    oci_fetch($s);
    return $value;
}

// Clean up  here

$stmtarray = array(
    "drop table nescurtest"
);

foreach($stmtarray as $stmt) {
    $s = oci_parse($c,$stmt);
    $r = @oci_execute($s);
    if (!$r) {
        $msg = oci_error($s);
        echo $msg['message'],"\n";
    }
}
oci_close($c);
echo "Done\n";
?>
--EXPECTF--
-----------------------------------------------
Test with Nested Cursors
-----------------------------------------------
Fetch Row using Nested cursor Query
array(1) {
  [0]=>
  %unicode|string%(%d) "test0"
}
Fetch Row using Nested cursor Query
array(1) {
  [0]=>
  %unicode|string%(%d) "test1"
}
Fetch Row using Nested cursor Query
array(1) {
  [0]=>
  %unicode|string%(%d) "test2"
}
Fetch Row using Nested cursor Query
array(1) {
  [0]=>
  %unicode|string%(%d) "test3"
}
Fetch Row using Nested cursor Query
array(1) {
  [0]=>
  %unicode|string%(%d) "test4"
}
Fetch Row using Nested cursor Query
array(1) {
  [0]=>
  %unicode|string%(%d) "test5"
}
Fetch Row using Nested cursor Query
array(1) {
  [0]=>
  %unicode|string%(%d) "test6"
}
Fetch Row using Nested cursor Query
array(1) {
  [0]=>
  %unicode|string%(%d) "test7"
}
Fetch Row using Nested cursor Query
array(1) {
  [0]=>
  %unicode|string%(%d) "test8"
}
Fetch Row using Nested cursor Query
array(1) {
  [0]=>
  %unicode|string%(%d) "test9"
}
Number of roundtrips made with prefetch count 5 for 10 rows is  3
Done
