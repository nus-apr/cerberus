--TEST--
Bug #42859 (import always conflicts with internal classes)
--FILE--
<?php
namespace Foo;
class Ex {}

use Blah\Exception;
use Blah\Ex;
?>
--EXPECTF--
Fatal error: Cannot use Blah\Ex as Ex because the name is already in use in %s.php on line 6
