#!/usr/bin/env perl
BEGIN {
	# add current source dir to the include-path
	# we need this for make distcheck
	(my $srcdir = $0) =~ s,/[^/]+$,/,;
	unshift @INC, $srcdir;
}

use strict;
use IO::Socket;
use Test::More tests => 3;
use LightyTest;

my $tf = LightyTest->new();
my $t;

ok($tf->start_proc == 0, "Starting lighttpd") or die();
$t->{REQUEST}  = ( <<EOF
GET /12345.txt HTTP/1.0
Host: 123.example.org
Range: bytes=-0
EOF
 );
$t->{RESPONSE} = [ { 'HTTP-Protocol' => 'HTTP/1.0', 'HTTP-Status' => 416, 'HTTP-Content' => <<EOF
<?xml version="1.0" encoding="iso-8859-1"?>
<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN"
         "http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">
<html xmlns="http://www.w3.org/1999/xhtml" xml:lang="en" lang="en">
 <head>
  <title>416 - Requested Range Not Satisfiable</title>
 </head>
 <body>
  <h1>416 - Requested Range Not Satisfiable</h1>
 </body>
</html>
EOF
 } ];
ok($tf->handle_http($t) == 0, 'GET, Range -0');

ok($tf->stop_proc == 0, "Stopping lighttpd");
