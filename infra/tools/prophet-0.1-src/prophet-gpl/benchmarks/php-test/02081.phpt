--TEST--
Gettext basic test
--SKIPIF--
<?php 
	if (!extension_loaded("gettext")) {
		die("skip\n");
	}
	if (!setlocale(LC_ALL, 'fi_FI')) {
		die("skip fi_FI locale not supported.");
	}
?>
--FILE--
<?php // $Id: gettext_basic.phpt 159732 2004-05-26 18:18:14Z iliaa $

chdir(dirname(__FILE__));
setlocale(LC_ALL, 'fi_FI');
bindtextdomain ("messages", "./locale");
textdomain ("messages");
echo gettext("Basic test"), "\n";
echo _("Basic test"), "\n";

?>
--EXPECT--
Perustesti
Perustesti
