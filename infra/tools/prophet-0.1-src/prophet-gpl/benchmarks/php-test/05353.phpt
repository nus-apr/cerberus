--TEST--
mysql_field_type()
--SKIPIF--
<?php
require_once('skipif.inc');
require_once('skipifconnectfailure.inc');
?>
--FILE--
<?php
include "connect.inc";

$tmp    = NULL;
$link   = NULL;

if (!is_null($tmp = @mysql_field_type()))
	printf("[001] Expecting NULL, got %s/%s\n", gettype($tmp), $tmp);

if (null !== ($tmp = @mysql_field_type($link)))
	printf("[002] Expecting NULL, got %s/%s\n", gettype($tmp), $tmp);

require('table.inc');
if (!$res = mysql_query("SELECT id, label FROM test ORDER BY id LIMIT 2", $link)) {
	printf("[003] [%d] %s\n", mysql_errno($link), mysql_error($link));
}

if (NULL !== ($tmp = mysql_field_type($res)))
	printf("[004] Expecting NULL, got %s/%s\n", gettype($tmp), $tmp);

if (false !== ($tmp = mysql_field_type($res, -1)))
	printf("[005] Expecting boolean/false, got %s/%s\n", gettype($tmp), $tmp);

var_dump(mysql_field_type($res, 0));

if (false !== ($tmp = mysql_field_type($res, 2)))
	printf("[008] Expecting boolean/false, got %s/%s\n", gettype($tmp), $tmp);

mysql_free_result($res);

var_dump(mysql_field_type($res, 0));

mysql_close($link);
print "done!";
?>
--CLEAN--
<?php
require_once("clean_table.inc");
?>
--EXPECTF--
Warning: mysql_field_type() expects exactly 2 parameters, 1 given in %s on line %d

Warning: mysql_field_type(): Field -1 is invalid for MySQL result index %d in %s on line %d
%unicode|string%(3) "int"

Warning: mysql_field_type(): Field 2 is invalid for MySQL result index %d in %s on line %d

Warning: mysql_field_type(): %d is not a valid MySQL result resource in %s on line %d
bool(false)
done!
