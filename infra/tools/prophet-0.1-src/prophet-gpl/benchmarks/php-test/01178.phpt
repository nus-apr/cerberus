--TEST--
GC 030: GC and exceptions in destructors
--INI--
zend.enable_gc=1
--FILE--
<?php
class foo {
    public $foo;

    public function __destruct() {
        throw new Exception("foobar");
    }
}

$f1 = new foo;
$f2 = new foo;
$f1->foo = $f2;
$f2->foo = $f1;
unset($f1, $f2);
gc_collect_cycles();
?>
--EXPECTF--
Fatal error: Uncaught exception 'Exception' with message 'foobar' in %s.php:%d
Stack trace:
#0 [internal function]: foo->__destruct()
#1 %s.php(%d): gc_collect_cycles()
#2 {main}

Next exception 'Exception' with message 'foobar' in %s.php:%d
Stack trace:
#0 %s.php(%d): foo->__destruct()
#1 {main}
  thrown in %s.php on line %d
