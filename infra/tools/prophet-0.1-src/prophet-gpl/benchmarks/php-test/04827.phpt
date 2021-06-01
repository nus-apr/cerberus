--TEST--
ReflectionClass and Traits
--FILE--
<?php
trait Foo {
    public function someMethod() { }
}

class Bar {
    use Foo;

    public function someOtherMethod() { }
}

$rFoo = new ReflectionClass('Foo');
$rBar = new ReflectionClass('Bar');

var_dump($rFoo->isTrait());
var_dump($rBar->isTrait());
echo $rFoo;
echo $rBar;
--EXPECTF--
bool(true)
bool(false)
Trait [ <user> trait Foo ] {
  @@ %s.php 2-4

  - Constants [0] {
  }

  - Static properties [0] {
  }

  - Static methods [0] {
  }

  - Properties [0] {
  }

  - Methods [1] {
    Method [ <user> public method someMethod ] {
      @@ %s.php 3 - 3
    }
  }
}
Class [ <user> class Bar ] {
  @@ %s.php 6-10

  - Constants [0] {
  }

  - Static properties [0] {
  }

  - Static methods [0] {
  }

  - Properties [0] {
  }

  - Methods [2] {
    Method [ <user> public method someOtherMethod ] {
      @@ %s.php 9 - 9
    }

    
    Method [ <user> public method someMethod ] {
      @@ %s.php 3 - 3
    }
  }
}
