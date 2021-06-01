--TEST--
029: Name ambiguity (class name & import name)
--FILE--
<?php
use A\B as Foo;

class Foo {
}

new Foo();
--EXPECTF--
Fatal error: Cannot declare class Foo because the name is already in use in %s.php on line 4
