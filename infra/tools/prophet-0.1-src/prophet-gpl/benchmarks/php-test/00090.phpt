--TEST--
Bug #23384 (use of class constants in statics)
--INI--
error_reporting=4095
--FILE--
<?php
define('TEN', 10);
class Foo {
    const HUN = 100;
    function test($x = Foo::HUN) {
        static $arr2 = array(TEN => 'ten');
        static $arr = array(Foo::HUN => 'ten');

        print_r($arr);
        print_r($arr2);
        print_r($x);
    }
}

Foo::test();   
echo Foo::HUN."\n";
?>
--EXPECTF--
Strict Standards: Non-static method Foo::test() should not be called statically in %s.php on line %d
Array
(
    [100] => ten
)
Array
(
    [10] => ten
)
100100
