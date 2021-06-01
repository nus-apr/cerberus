--TEST--
Test preg_split() function : error conditions - bad regular expressions
--FILE--
<?php
/*
* proto array preg_split(string pattern, string subject [, int limit [, int flags]])
* Function is implemented in ext/pcre/php_pcre.c
*/
error_reporting(E_ALL&~E_NOTICE);
/*
* Testing how preg_split reacts to being passed the wrong type of regex argument
*/
echo "*** Testing preg_split() : error conditions ***\n";
$regex_array = array('abcdef', //Regex without delimiter
'/[a-zA-Z]', //Regex without closing delimiter
'[a-zA-Z]/', //Regex without opening delimiter
'/[a-zA-Z]/F', array('[a-z]', //Array of Regexes
'[A-Z]', '[0-9]'), '/[a-zA-Z]/', //Regex string
);
$subject = '1 2 a 3 4 b 5 6';
foreach($regex_array as $regex_value) {
    print "\nArg value is $regex_value\n";
    var_dump(preg_split($regex_value, $subject));
}
$regex_value = new stdclass(); //Object
var_dump(preg_split($regex_value, $subject));
?>
--EXPECTF--
*** Testing preg_split() : error conditions ***

Arg value is abcdef

Warning: preg_split(): Delimiter must not be alphanumeric or backslash in %s.php on line %d
bool(false)

Arg value is /[a-zA-Z]

Warning: preg_split(): No ending delimiter '/' found in %s.php on line %d
bool(false)

Arg value is [a-zA-Z]/

Warning: preg_split(): Unknown modifier '/' in %s.php on line %d
bool(false)

Arg value is /[a-zA-Z]/F

Warning: preg_split(): Unknown modifier 'F' in %s.php on line %d
bool(false)

Arg value is Array

Warning: preg_split() expects parameter 1 to be string, array given in %s.php on line %d
bool(false)

Arg value is /[a-zA-Z]/
array(3) {
  [0]=>
  string(4) "1 2 "
  [1]=>
  string(5) " 3 4 "
  [2]=>
  string(4) " 5 6"
}

Warning: preg_split() expects parameter 1 to be string, object given in %s.php on line %d
bool(false)
