--TEST--
Bug #45805 (Crash on throwing exception from error handler)
--SKIPIF--
<?php extension_loaded('reflection') or die('skip'); ?>
--FILE--
<?php
class PHPUnit_Util_ErrorHandler
{
    public static function handleError($errno, $errstr, $errfile, $errline)
    {
        throw new RuntimeException;
    }
}

class A {
    public function getX() {
        return NULL;
    }
}

class B {
    public function foo() {
        $obj    = new A;
        $source = &$obj->getX();
    }

    public function bar() {
        $m = new ReflectionMethod('B', 'foo');
        $m->invoke($this);
    }
}

set_error_handler(
  array('PHPUnit_Util_ErrorHandler', 'handleError'), E_ALL | E_STRICT
);
            
$o = new B;
$o->bar();
?>
--EXPECTF--
Fatal error: Uncaught exception 'RuntimeException' in %s.php:%d
Stack trace:
#0 %s.php(%d): PHPUnit_Util_ErrorHandler::handleError(2048, 'Only variables ...', '%s', %d, Array)
#1 [internal function]: B->foo()
#2 %s.php(%d): ReflectionMethod->invoke(Object(B))
#3 %s.php(%d): B->bar()
#4 {main}
  thrown in %s.php on line %d
