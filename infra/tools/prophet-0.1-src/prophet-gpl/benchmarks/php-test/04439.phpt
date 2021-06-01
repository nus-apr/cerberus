--TEST--
Test session_register() function : variation
--SKIPIF--
<?php include('skipif.inc'); if(PHP_VERSION_ID < 503099) { die('SKIP'); } ?>
--FILE--
<?php

ob_start();

/* 
 * Prototype : bool session_register(mixed $name [,mixed $...])
 * Description : Register one or more global variables with the current session
 * Source code : ext/session/session.c 
 */

echo "*** Testing session_register() : variation ***\n";

var_dump(session_start());
var_dump($_SESSION);
var_dump(session_register());
var_dump($_SESSION);
var_dump(session_destroy());
var_dump($_SESSION);

echo "Done";
ob_end_flush();
?>
--EXPECTF--
*** Testing session_register() : variation ***
bool(true)
array(0) {
}

Deprecated: Function session_register() is deprecated in %s on line %d

Warning: session_register() expects at least 1 parameter, 0 given in %s on line %d
NULL
array(0) {
}
bool(true)
array(0) {
}
Done
