--TEST--
Bug #51709 (Can't use keywords as method names)
--FILE--
<?php

class foo {
        static function for() {
                echo "1";
        }
}

?>
===DONE===
<?php exit(0); ?>
--EXPECTF--
Parse error: syntax error, unexpected T_FOR, expecting T_STRING in %s.php on line %d
