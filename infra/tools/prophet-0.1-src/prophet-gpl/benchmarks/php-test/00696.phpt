--TEST--
Bug #46313 (Magic quotes broke $_FILES)
--SKIPIF--
<?php if(substr(PHP_OS, 0, 3) == "WIN") die("skip non-Windows test"); ?>
--INI--
magic_quotes_gpc=1
file_uploads=1
display_errors=0
--POST_RAW--
Content-Type: multipart/form-data; boundary=---------------------------20896060251896012921717172737
-----------------------------20896060251896012921717172737
Content-Disposition: form-data; name="o1'file"; filename="o1'file.png"
Content-Type: text/plain-file1

1
-----------------------------20896060251896012921717172737
Content-Disposition: form-data; name="o2'file"; filename="o2'file2.txt"
Content-Type: text/plain-file2

2
-----------------------------20896060251896012921717172737--
--FILE--
<?php
var_dump($_FILES);
?>
--EXPECTF--
array(2) {
  ["o1\'file"]=>
  array(5) {
    ["name"]=>
    string(12) "o1\'file.png"
    ["type"]=>
    string(16) "text/plain-file1"
    ["tmp_name"]=>
    string(%d) "%s"
    ["error"]=>
    int(0)
    ["size"]=>
    int(1)
  }
  ["o2\'file"]=>
  array(5) {
    ["name"]=>
    string(13) "o2\'file2.txt"
    ["type"]=>
    string(16) "text/plain-file2"
    ["tmp_name"]=>
    string(%d) "%s"
    ["error"]=>
    int(0)
    ["size"]=>
    int(1)
  }
}
