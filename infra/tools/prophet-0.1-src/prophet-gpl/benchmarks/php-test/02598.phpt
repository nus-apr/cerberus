--TEST--
Bug #37346 (gdimagecreatefromgif, bad colormap)
--SKIPIF--
<?php
	if (!extension_loaded('gd')) die("skip gd extension not available\n");
?>
--FILE--
<?php
$im = imagecreatefromgif(dirname(__FILE__) . '/bug37346.gif');
?>
--EXPECTF--
Warning: imagecreatefromgif(): '%sbug37346.gif' is not a valid GIF file in %s.php on line %d
