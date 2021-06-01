--TEST--
Phar: delete a file within a tar-based .phar
--SKIPIF--
<?php if (!extension_loaded("phar")) die("skip"); ?>
--INI--
phar.readonly=0
phar.require_hash=0
--FILE--
<?php

$fname = dirname(__FILE__) . '/' . basename(__FILE__, '.php') . '.phar.tar';
$alias = 'phar://' . $fname;

$phar = new Phar($fname);
$phar['a.php'] = '<?php echo "This is a\n"; ?>';
$phar['b.php'] = '<?php echo "This is b\n"; ?>';
$phar['b/c.php'] = '<?php echo "This is b/c\n"; ?>';
$phar->setStub('<?php __HALT_COMPILER(); ?>');
$phar->stopBuffering();

include $alias . '/a.php';
include $alias . '/b.php';
include $alias . '/b/c.php';
unlink($alias . '/b/c.php');

?>
===AFTER===
<?php
include $alias . '/a.php';
include $alias . '/b.php';
include $alias . '/b/c.php';
?>

===DONE===
--CLEAN--
<?php unlink(dirname(__FILE__) . '/' . basename(__FILE__, '.clean.php') . '.phar.tar'); ?>
--EXPECTF--
This is a
This is b
This is b/c
===AFTER===
This is a
This is b

Warning: include(%s.php): failed to open stream: phar error: "b/c.php" is not a file in phar "%sdelete_in_phar.phar.tar" in %s.php on line %d

Warning: include(): Failed opening 'phar://%s.php' for inclusion (include_path='%s') in %s.php on line %d

===DONE===
