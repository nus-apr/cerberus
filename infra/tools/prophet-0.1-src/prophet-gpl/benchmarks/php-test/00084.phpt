--TEST--
Dynamic call for static methods
--FILE--
<?php
class A {
    static function foo() { return 'foo'; }
}

$classname       =  'A';
$wrongClassname  =  'B';

echo $classname::foo()."\n";
echo $wrongClassname::foo()."\n";
?>
===DONE===
--EXPECTF--
foo

Fatal error: Class 'B' not found in %s.php on line %d
