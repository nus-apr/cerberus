--TEST--
Bug #37799 (ftp_ssl_connect() falls back to non-ssl connection)
--SKIPIF--
<?php
$ssl = 1;
require 'skipif.inc';
?>
--FILE--
<?php
$bug37799=$ssl=1;
require 'server.inc';

$ftp = ftp_ssl_connect('127.0.0.1', $port);
if (!$ftp) die("Couldn't connect to the server");

var_dump(ftp_login($ftp, 'user', 'pass'));

ftp_close($ftp);
?>
--EXPECTF--
Warning: ftp_login(): bogus msg in %s.php on line 8
bool(false)
