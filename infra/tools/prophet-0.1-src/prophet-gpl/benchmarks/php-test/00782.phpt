--TEST--
Bug #53511 (Exceptions are lost in case an exception is thrown in catch operator)
--FILE--
<?php
class Foo {
	function __destruct() {
		throw new Exception("ops 1");
	}
}

function test() {
	$e = new Foo();
	try {
		throw new Exception("ops 2");
	} catch (Exception $e) {
		echo $e->getMessage()."\n";
	}
}

test();
echo "bug\n";
--EXPECTF--
Fatal error: Uncaught exception 'Exception' with message 'ops 2' in %s.php:11
Stack trace:
#0 %s.php(17): test()
#1 {main}

Next exception 'Exception' with message 'ops 1' in %s.php:4
Stack trace:
#0 %s.php(12): Foo->__destruct()
#1 %s.php(17): test()
#2 {main}
  thrown in %s.php on line 4
