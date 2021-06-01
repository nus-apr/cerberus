--TEST--
Test 3: Exception Test
--SKIPIF--
<?php require_once('skipif.inc'); ?>
--FILE--
<?php

$dom = new domdocument;
$dom->load(dirname(__FILE__)."/book.xml");
$rootNode = $dom->documentElement;
print "--- Catch exception with try/catch\n";
try {
    $rootNode->appendChild($rootNode);
} catch (domexception $e) {
    var_dump($e);
}
print "--- Don't catch exception with try/catch\n";
$rootNode->appendChild($rootNode);


?>
--EXPECTF--
--- Catch exception with try/catch
object(DOMException)#%d (%d) {
  ["message":protected]=>
  string(23) "Hierarchy Request Error"
  ["string":"Exception":private]=>
  string(0) ""
  ["file":protected]=>
  string(%d) "%s.php"
  ["line":protected]=>
  int(8)
  ["trace":"Exception":private]=>
  array(1) {
    [0]=>
    array(6) {
      ["file"]=>
      string(%d) "%s.php"
      ["line"]=>
      int(8)
      ["function"]=>
      string(11) "appendChild"
      ["class"]=>
      string(7) "DOMNode"
      ["type"]=>
      string(2) "->"
      ["args"]=>
      array(1) {
        [0]=>
        object(DOMElement)#%d (0) {
        }
      }
    }
  }
  ["previous":"Exception":private]=>
  NULL
  ["code"]=>
  int(3)
}
--- Don't catch exception with try/catch

Fatal error: Uncaught exception 'DOMException' with message 'Hierarchy Request Error' in %s.php:%d
Stack trace:
#0 %s.php(13): DOMNode->appendChild(Object(DOMElement))
#1 {main}
  thrown in %s.php on line %d
