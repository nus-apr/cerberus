<?php
class MyClass {
	public $myRef;
	public function __get($property) {
        $this->myRef = "ok\n";
        return "a";
	}
}
$myGlobal=new MyClass($myGlobal);
$myGlobal->myRef=&$myGlobal;
$a = $myGlobal->myNonExistentProperty;
echo $myGlobal;
?>
