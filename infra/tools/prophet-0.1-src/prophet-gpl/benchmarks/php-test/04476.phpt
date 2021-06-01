--TEST--
Test session_unregister() function : basic functionality
--SKIPIF--
<?php include('skipif.inc'); if(PHP_VERSION_ID < 503099) { die('SKIP'); } ?>
--FILE--
<?php

ob_start();

/* 
 * Prototype : bool session_is_registered(string $name)
 * Description : Find out whether a global variable is registered in a session
 * Source code : ext/session/session.c 
 */

echo "*** Testing session_is_registered() : basic functionality ***\n";

// Get an unset variable
$unset_var = 10;
unset($unset_var);

class classA
{
    public function __toString() {
        return "Hello World!";
    }
}

$heredoc = <<<EOT
Hello World!
EOT;

$fp = fopen(__FILE__, "r");

// Unexpected values to be passed as arguments
$inputs = array(

       // Integer data
/*1*/  0,
       1,
       12345,
       -2345,

       // Float data
/*5*/  10.5,
       -10.5,
       12.3456789000e10,
       12.3456789000E-10,
       .5,

       // Null data
/*10*/ NULL,
       null,

       // Boolean data
/*12*/ true,
       false,
       TRUE,
       FALSE,
       
       // Empty strings
/*16*/ "",
       '',

       // Invalid string data
/*18*/ "Nothing",
       'Nothing',
       $heredoc,
       
       // Object data
/*21*/ new classA(),

       // Undefined data
/*22*/ @$undefined_var,

       // Unset data
/*23*/ @$unset_var,

       // Resource variable
/*24*/ $fp
);


$iterator = 1;
foreach($inputs as $input) {
    echo "\n-- Iteration $iterator --\n";
    var_dump(session_start());
    var_dump(session_is_registered($input));
    var_dump($_SESSION);
    var_dump(session_destroy());
    $iterator++;
};

fclose($fp);
echo "Done";
ob_end_flush();
?>
--EXPECTF--
*** Testing session_is_registered() : basic functionality ***

-- Iteration 1 --
bool(true)

Deprecated: Function session_is_registered() is deprecated in %s on line %d
bool(false)
array(0) {
}
bool(true)

-- Iteration 2 --
bool(true)

Deprecated: Function session_is_registered() is deprecated in %s on line %d
bool(false)
array(0) {
}
bool(true)

-- Iteration 3 --
bool(true)

Deprecated: Function session_is_registered() is deprecated in %s on line %d
bool(false)
array(0) {
}
bool(true)

-- Iteration 4 --
bool(true)

Deprecated: Function session_is_registered() is deprecated in %s on line %d
bool(false)
array(0) {
}
bool(true)

-- Iteration 5 --
bool(true)

Deprecated: Function session_is_registered() is deprecated in %s on line %d
bool(false)
array(0) {
}
bool(true)

-- Iteration 6 --
bool(true)

Deprecated: Function session_is_registered() is deprecated in %s on line %d
bool(false)
array(0) {
}
bool(true)

-- Iteration 7 --
bool(true)

Deprecated: Function session_is_registered() is deprecated in %s on line %d
bool(false)
array(0) {
}
bool(true)

-- Iteration 8 --
bool(true)

Deprecated: Function session_is_registered() is deprecated in %s on line %d
bool(false)
array(0) {
}
bool(true)

-- Iteration 9 --
bool(true)

Deprecated: Function session_is_registered() is deprecated in %s on line %d
bool(false)
array(0) {
}
bool(true)

-- Iteration 10 --
bool(true)

Deprecated: Function session_is_registered() is deprecated in %s on line %d
bool(false)
array(0) {
}
bool(true)

-- Iteration 11 --
bool(true)

Deprecated: Function session_is_registered() is deprecated in %s on line %d
bool(false)
array(0) {
}
bool(true)

-- Iteration 12 --
bool(true)

Deprecated: Function session_is_registered() is deprecated in %s on line %d
bool(false)
array(0) {
}
bool(true)

-- Iteration 13 --
bool(true)

Deprecated: Function session_is_registered() is deprecated in %s on line %d
bool(false)
array(0) {
}
bool(true)

-- Iteration 14 --
bool(true)

Deprecated: Function session_is_registered() is deprecated in %s on line %d
bool(false)
array(0) {
}
bool(true)

-- Iteration 15 --
bool(true)

Deprecated: Function session_is_registered() is deprecated in %s on line %d
bool(false)
array(0) {
}
bool(true)

-- Iteration 16 --
bool(true)

Deprecated: Function session_is_registered() is deprecated in %s on line %d
bool(false)
array(0) {
}
bool(true)

-- Iteration 17 --
bool(true)

Deprecated: Function session_is_registered() is deprecated in %s on line %d
bool(false)
array(0) {
}
bool(true)

-- Iteration 18 --
bool(true)

Deprecated: Function session_is_registered() is deprecated in %s on line %d
bool(false)
array(0) {
}
bool(true)

-- Iteration 19 --
bool(true)

Deprecated: Function session_is_registered() is deprecated in %s on line %d
bool(false)
array(0) {
}
bool(true)

-- Iteration 20 --
bool(true)

Deprecated: Function session_is_registered() is deprecated in %s on line %d
bool(false)
array(0) {
}
bool(true)

-- Iteration 21 --
bool(true)

Deprecated: Function session_is_registered() is deprecated in %s on line %d
bool(false)
array(0) {
}
bool(true)

-- Iteration 22 --
bool(true)

Deprecated: Function session_is_registered() is deprecated in %s on line %d
bool(false)
array(0) {
}
bool(true)

-- Iteration 23 --
bool(true)

Deprecated: Function session_is_registered() is deprecated in %s on line %d
bool(false)
array(0) {
}
bool(true)

-- Iteration 24 --
bool(true)

Deprecated: Function session_is_registered() is deprecated in %s on line %d

Warning: session_is_registered() expects parameter 1 to be string, resource given in %s on line %d
NULL
array(0) {
}
bool(true)
Done
