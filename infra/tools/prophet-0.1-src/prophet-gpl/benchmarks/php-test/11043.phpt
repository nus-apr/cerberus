--TEST--
posix_getpwnam(): Basic tests
--SKIPIF--
<?php
if (!extension_loaded('posix')) die('skip - POSIX extension not loaded'); 
if (!function_exists('posix_getpwnam')) die('skip posix_getpwnam() not found');
?>
--FILE--
<?php

var_dump(posix_getpwnam(1));
var_dump(posix_getpwnam(''));
var_dump(posix_getpwnam(NULL));

?>
--EXPECT--
bool(false)
bool(false)
bool(false)
