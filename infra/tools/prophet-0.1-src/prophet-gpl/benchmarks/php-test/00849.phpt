--TEST--
unset() CV 5 (indirect unset() of global variable in session_start())
--INI--
session.auto_start=0
session.save_handler=files
--SKIPIF--
<?php 

include(dirname(__FILE__).'/../../ext/session/tests/skipif.inc'); 

?>
--FILE--
<?php
$_SESSION = "ok\n";
echo $_SESSION;
session_start();
echo $_SESSION;
echo "\nok\n";
?>
--EXPECTF--
ok

Warning: session_start(): Cannot send session cookie - headers already sent by (output started at %s.php on line %d

Warning: session_start(): Cannot send session cache limiter - headers already sent (output started at %s.php:%d) in %s.php on line %d
Array
ok
