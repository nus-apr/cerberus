--TEST--
filter_list()
--SKIPIF--
<?php if (!extension_loaded("filter")) die("skip"); ?>
--FILE--
<?php

var_dump(filter_list());
var_dump(filter_list(array()));

echo "Done\n";
?>
--EXPECTF--	
array(19) {
  [0]=>
  string(3) "int"
  [1]=>
  string(7) "boolean"
  [2]=>
  string(5) "float"
  [3]=>
  string(15) "validate_regexp"
  [4]=>
  string(12) "validate_url"
  [5]=>
  string(14) "validate_email"
  [6]=>
  string(11) "validate_ip"
  [7]=>
  string(6) "string"
  [8]=>
  string(8) "stripped"
  [9]=>
  string(7) "encoded"
  [10]=>
  string(13) "special_chars"
  [11]=>
  string(18) "full_special_chars"
  [12]=>
  string(10) "unsafe_raw"
  [13]=>
  string(5) "email"
  [14]=>
  string(3) "url"
  [15]=>
  string(10) "number_int"
  [16]=>
  string(12) "number_float"
  [17]=>
  string(12) "magic_quotes"
  [18]=>
  string(8) "callback"
}

Warning: filter_list() expects exactly 0 parameters, 1 given in %s on line %d
NULL
Done
