--TEST--
Test spliti() function : usage variations  - unexpected type for arg 1
--FILE--
<?php
/* Prototype  : proto array spliti(string pattern, string string [, int limit])
 * Description: spliti string into array by regular expression 
 * Source code: ext/standard/reg.c
 * Alias to functions: 
 */

function test_error_handler($err_no, $err_msg, $filename, $linenum, $vars) {
	echo "Error: $err_no - $err_msg, $filename($linenum)\n";
}
set_error_handler('test_error_handler');

echo "*** Testing spliti() : usage variations ***\n";

// Initialise function arguments not being substituted (if any)
$string = '1 a 1 Array 1 c ';
$limit = 5;

//get an unset variable
$unset_var = 10;
unset ($unset_var);

//array of values to iterate over
$values = array(

      // int data
      0,
      1,
      12345,
      -2345,

      // float data
      10.5,
      -10.5,
      10.1234567e10,
      10.7654321E-10,
      .5,

      // array data
      array(),
      array(0),
      array(1),
      array(1, 2),
      array('color' => 'red', 'item' => 'pen'),

      // null data
      NULL,
      null,

      // boolean data
      true,
      false,
      TRUE,
      FALSE,

      // empty data
      "",
      '',

      // object data
      new stdclass(),

      // undefined data
      $undefined_var,

      // unset data
      $unset_var,
);

// loop through each element of the array for pattern

foreach($values as $value) {
      echo "\nArg value $value \n";
      var_dump( spliti($value, $string, $limit) );
};

echo "Done";
?>
--EXPECTF--
*** Testing spliti() : usage variations ***
Error: 8 - Undefined variable: undefined_var, %s(64)
Error: 8 - Undefined variable: unset_var, %s(67)

Arg value 0 
Error: 8192 - Function spliti() is deprecated, %s(74)
array(1) {
  [0]=>
  string(16) "1 a 1 Array 1 c "
}

Arg value 1 
Error: 8192 - Function spliti() is deprecated, %s(74)
array(4) {
  [0]=>
  string(0) ""
  [1]=>
  string(3) " a "
  [2]=>
  string(7) " Array "
  [3]=>
  string(3) " c "
}

Arg value 12345 
Error: 8192 - Function spliti() is deprecated, %s(74)
array(1) {
  [0]=>
  string(16) "1 a 1 Array 1 c "
}

Arg value -2345 
Error: 8192 - Function spliti() is deprecated, %s(74)
array(1) {
  [0]=>
  string(16) "1 a 1 Array 1 c "
}

Arg value 10.5 
Error: 8192 - Function spliti() is deprecated, %s(74)
array(1) {
  [0]=>
  string(16) "1 a 1 Array 1 c "
}

Arg value -10.5 
Error: 8192 - Function spliti() is deprecated, %s(74)
array(1) {
  [0]=>
  string(16) "1 a 1 Array 1 c "
}

Arg value 101234567000 
Error: 8192 - Function spliti() is deprecated, %s(74)
array(1) {
  [0]=>
  string(16) "1 a 1 Array 1 c "
}

Arg value 1.07654321E-9 
Error: 8192 - Function spliti() is deprecated, %s(74)
array(1) {
  [0]=>
  string(16) "1 a 1 Array 1 c "
}

Arg value 0.5 
Error: 8192 - Function spliti() is deprecated, %s(74)
array(1) {
  [0]=>
  string(16) "1 a 1 Array 1 c "
}

Arg value Array 
Error: 8192 - Function spliti() is deprecated, %s(74)
Error: 2 - spliti() expects parameter 1 to be string, array given, %s(74)
NULL

Arg value Array 
Error: 8192 - Function spliti() is deprecated, %s(74)
Error: 2 - spliti() expects parameter 1 to be string, array given, %s(74)
NULL

Arg value Array 
Error: 8192 - Function spliti() is deprecated, %s(74)
Error: 2 - spliti() expects parameter 1 to be string, array given, %s(74)
NULL

Arg value Array 
Error: 8192 - Function spliti() is deprecated, %s(74)
Error: 2 - spliti() expects parameter 1 to be string, array given, %s(74)
NULL

Arg value Array 
Error: 8192 - Function spliti() is deprecated, %s(74)
Error: 2 - spliti() expects parameter 1 to be string, array given, %s(74)
NULL

Arg value  
Error: 8192 - Function spliti() is deprecated, %s(74)
Error: 2 - spliti(): REG_EMPTY, %s(74)
bool(false)

Arg value  
Error: 8192 - Function spliti() is deprecated, %s(74)
Error: 2 - spliti(): REG_EMPTY, %s(74)
bool(false)

Arg value 1 
Error: 8192 - Function spliti() is deprecated, %s(74)
array(4) {
  [0]=>
  string(0) ""
  [1]=>
  string(3) " a "
  [2]=>
  string(7) " Array "
  [3]=>
  string(3) " c "
}

Arg value  
Error: 8192 - Function spliti() is deprecated, %s(74)
Error: 2 - spliti(): REG_EMPTY, %s(74)
bool(false)

Arg value 1 
Error: 8192 - Function spliti() is deprecated, %s(74)
array(4) {
  [0]=>
  string(0) ""
  [1]=>
  string(3) " a "
  [2]=>
  string(7) " Array "
  [3]=>
  string(3) " c "
}

Arg value  
Error: 8192 - Function spliti() is deprecated, %s(74)
Error: 2 - spliti(): REG_EMPTY, %s(74)
bool(false)

Arg value  
Error: 8192 - Function spliti() is deprecated, %s(74)
Error: 2 - spliti(): REG_EMPTY, %s(74)
bool(false)

Arg value  
Error: 8192 - Function spliti() is deprecated, %s(74)
Error: 2 - spliti(): REG_EMPTY, %s(74)
bool(false)
Error: 4096 - Object of class stdClass could not be converted to string, %s(73)

Arg value  
Error: 8192 - Function spliti() is deprecated, %s(74)
Error: 2 - spliti() expects parameter 1 to be string, object given, %s(74)
NULL

Arg value  
Error: 8192 - Function spliti() is deprecated, %s(74)
Error: 2 - spliti(): REG_EMPTY, %s(74)
bool(false)

Arg value  
Error: 8192 - Function spliti() is deprecated, %s(74)
Error: 2 - spliti(): REG_EMPTY, %s(74)
bool(false)
Done
