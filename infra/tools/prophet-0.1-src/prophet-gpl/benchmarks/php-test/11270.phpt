--TEST--
Test split() function : basic functionality - a few non-matches
--FILE--
<?php
/* Prototype  : proto array split(string pattern, string string [, int limit])
 * Description: split string into array by regular expression 
 * Source code: ext/standard/reg.c
 * Alias to functions: 
 */

$replacement = 'r';

var_dump(split('A', '-- a --'));
var_dump(split('[A-Z]', '-- 0 --'));
var_dump(split('(a){4}', '--- aaa ---'));
var_dump(split('^a', '--- ba ---'));
var_dump(split('b$', '--- ba ---'));
var_dump(split('[:alpha:]', '--- x ---'));


echo "Done";
?>
--EXPECTF--
Deprecated: Function split() is deprecated in %s on line %d
array(1) {
  [0]=>
  string(7) "-- a --"
}

Deprecated: Function split() is deprecated in %s on line %d
array(1) {
  [0]=>
  string(7) "-- 0 --"
}

Deprecated: Function split() is deprecated in %s on line %d
array(1) {
  [0]=>
  string(11) "--- aaa ---"
}

Deprecated: Function split() is deprecated in %s on line %d
array(1) {
  [0]=>
  string(10) "--- ba ---"
}

Deprecated: Function split() is deprecated in %s on line %d
array(1) {
  [0]=>
  string(10) "--- ba ---"
}

Deprecated: Function split() is deprecated in %s on line %d
array(1) {
  [0]=>
  string(9) "--- x ---"
}
Done
