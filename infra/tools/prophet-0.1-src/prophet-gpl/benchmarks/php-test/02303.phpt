--TEST--
Check that bad argumens return the same
--SKIPIF--
<?php if( !extension_loaded( 'intl' ) ) print 'skip'; ?>
--FILE--
<?php
$funcs = get_extension_funcs("intl");
function ignore_err() {}
set_error_handler("ignore_err");
$arg = new stdClass();
foreach($funcs as $func) {
        $rfunc = new ReflectionFunction($func);
        if($rfunc->getNumberOfRequiredParameters() == 0) {
                continue;
        }
        $res = $func($arg);
        if($res != false) {
                echo "$func: ";
                var_dump($res);
        }
}
echo "OK!\n";
?>
--EXPECT--
OK!
