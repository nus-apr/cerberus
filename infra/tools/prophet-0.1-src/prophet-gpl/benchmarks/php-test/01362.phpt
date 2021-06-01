--TEST--
exception handler tests - 2
--FILE--
<?php

set_exception_handler("foo");

function foo($e) {
	var_dump(get_class($e)." thrown!");
	throw new Exception();
}

class test extends Exception {
}

throw new test();

echo "Done\n";
?>
--EXPECTF--	
string(12) "test thrown!"

Fatal error: Uncaught exception 'Exception' in %s.php:7
Stack trace:
#0 [internal function]: foo(Object(test))
#1 {main}
  thrown in %s.php on line %d
