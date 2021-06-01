--TEST--
Setting previous exception
--FILE--
<?php

try {
	try {
		throw new Exception("First", 1, new Exception("Another", 0, NULL));
	}
	catch (Exception $e) {
		throw new Exception("Second", 2, $e);
	}
}
catch (Exception $e) {
	throw new Exception("Third", 3, $e);
}

?>
===DONE===
--EXPECTF--
Fatal error: Uncaught exception 'Exception' with message 'Another' in %s.php:%d
Stack trace:
#0 {main}

Next exception 'Exception' with message 'First' in %s.php:%d
Stack trace:
#0 {main}

Next exception 'Exception' with message 'Second' in %s.php:%d
Stack trace:
#0 {main}

Next exception 'Exception' with message 'Third' in %s.php:%d
Stack trace:
#0 {main}
  thrown in %s.php on line %d
