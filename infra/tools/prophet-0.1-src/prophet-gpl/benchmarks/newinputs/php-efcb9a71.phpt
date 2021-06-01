--TEST--
New test case for efcb9a71
--FILE--
<?php
static $s = 'ahaha';
$rs = &$s;

$clo = function() use($rs){
	echo "$rs\n";
};

$rs = 'ahaha2';
echo "$rs\n";
echo "$s\n";
unset($s);
unset($rs);
$clo();?>
--EXPECT--
ahaha2
ahaha2
ahaha
