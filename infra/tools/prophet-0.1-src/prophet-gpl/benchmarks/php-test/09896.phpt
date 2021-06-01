--TEST--
Phar front controller mime type unknown int
--INI--
default_charset=UTF-8
--SKIPIF--
<?php if (!extension_loaded("phar")) die("skip"); ?>
--ENV--
SCRIPT_NAME=/frontcontroller12.php
REQUEST_URI=/frontcontroller12.php/a.php
PATH_INFO=/a.php
--FILE_EXTERNAL--
files/frontcontroller6.phar
--EXPECTHEADERS--
Content-type: text/html; charset=UTF-8
--EXPECTF--
Fatal error: Uncaught exception 'PharException' with message 'Unknown mime type specifier used, only Phar::PHP, Phar::PHPS and a mime type string are allowed' in %s.php:2
Stack trace:
#0 %s.php(2): Phar::webPhar('whatever', 'index.php', '', Array)
#1 {main}
  thrown in %s.php on line 2