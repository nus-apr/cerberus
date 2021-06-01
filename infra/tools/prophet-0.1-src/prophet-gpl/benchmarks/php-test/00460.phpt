--TEST--
ZE2 __toString() in __destruct/exception
--FILE--
<?php

class Test
{
	function __toString()
	{
		throw new Exception("Damn!");
		return "Hello\n";
	}
	
	function __destruct()
	{
		echo $this;
	}
}

try
{
	$o = new Test;
	$o = NULL;
}
catch(Exception $e)
{
	var_dump($e->getMessage());
}

?>
====DONE====
--EXPECTF--
Fatal error: Method Test::__toString() must not throw an exception in %s.php on line %d
