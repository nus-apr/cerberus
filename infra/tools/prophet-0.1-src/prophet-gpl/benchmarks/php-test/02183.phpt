--TEST--
zlib.deflate (with convert.base64-encode)
--SKIPIF--
<?php if (!extension_loaded("zlib")) print "skip"; ?>
--FILE--
<?php /* $Id: zlib_filter_deflate.phpt 201145 2005-11-24 04:37:47Z pollita $ */
$text = 'I am the very model of a modern major general, I\'ve information vegetable, animal, and mineral.';

$fp = fopen('php://stdout', 'w');
stream_filter_append($fp, 'zlib.deflate', STREAM_FILTER_WRITE);
stream_filter_append($fp, 'convert.base64-encode', STREAM_FILTER_WRITE);
fwrite($fp, $text);
fclose($fp);

?> 
--EXPECT-- 
HctBDoAgDETRq8zOjfEeHKOGATG0TRpC4u1Vdn/xX4IoxkVMxgP1zA4vkJVhULk9UGkM6TvSNolmxUNlNLePVQ45O3eINf0fsQxtCxwv
