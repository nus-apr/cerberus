--TEST--
CallbackFilterIterator 002
--FILE--
<?php

set_error_handler(function($errno, $errstr){
	echo $errstr . "\n";
	return true;
});

try {
	new CallbackFilterIterator();
} catch(InvalidArgumentException $e) {
	echo $e->getMessage() . "\n";
}

try {
	new CallbackFilterIterator(null);
} catch(InvalidArgumentException $e) {
	echo $e->getMessage() . "\n";
}

try {
	new CallbackFilterIterator(new ArrayIterator(array()), null);
} catch(InvalidArgumentException $e) {
	echo $e->getMessage() . "\n";
}

try {
	new CallbackFilterIterator(new ArrayIterator(array()), array());
} catch(InvalidArgumentException $e) {
	echo $e->getMessage() . "\n";
}

$it = new CallbackFilterIterator(new ArrayIterator(array(1)), function() {
	throw new Exception("some message");
});
try {
	foreach($it as $e);
} catch(Exception $e) {
	echo $e->getMessage() . "\n";
}

class Test extends CallbackFilterIterator {
	function __construct(){}
}
class Test2 extends RecursiveCallbackFilterIterator {
	function __construct(){}
}

try {
	new Test;
} catch(LogicException $e) {
	echo $e->getMessage() . "\n";
}

try {
	new Test2;
} catch(LogicException $e) {
	echo $e->getMessage() . "\n";
}

--EXPECT--
CallbackFilterIterator::__construct() expects exactly 2 parameters, 0 given
Argument 1 passed to CallbackFilterIterator::__construct() must implement interface Iterator, null given
CallbackFilterIterator::__construct() expects exactly 2 parameters, 1 given
CallbackFilterIterator::__construct() expects parameter 2 to be a valid callback, no array or string given
CallbackFilterIterator::__construct() expects parameter 2 to be a valid callback, array must have exactly two members
some message
In the constructor of Test, parent::__construct() must be called and its exceptions cannot be cleared
In the constructor of Test2, parent::__construct() must be called and its exceptions cannot be cleared
