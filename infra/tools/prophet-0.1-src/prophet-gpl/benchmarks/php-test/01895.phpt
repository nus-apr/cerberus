--TEST--
execute a file with -f
--SKIPIF--
<?php 
include "skipif.inc"; 
?>
--FILE--
<?php

include "include.inc";

$php = get_cgi_path();
reset_env_vars();

$filename = dirname(__FILE__).'/004.test.php';
$code ='
<?php

class test { 
	private $pri; 
}

var_dump(test::$pri);
?>
';

file_put_contents($filename, $code);

var_dump(`$php -n -f "$filename" 2>/dev/null`);
var_dump(`$php -n -f "wrong"`);

@unlink($filename);

echo "Done\n";
?>
--EXPECTF--	
string(%d) "
<br />
<b>Fatal error</b>:  Cannot access private property test::$pri in <b>%s.php</b> on line <b>8</b><br />
"
string(25) "No input file specified.
"
Done
