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
$t->{REQUEST} = ( <<EOF
GET /12345.txt HTTP/1.1
Host: 123.example.org

GET /12345.txt HTTP/1.1
Host: 123.example.org
Connection: close
EOF
 );

$t->{RESPONSE} = [ { 'HTTP-Protocol' => 'HTTP/1.1', 'HTTP-Status' => 200 } , { 'HTTP-Protocol' => 'HTTP/1.1', 'HTTP-Status' => 200 } ];

ok($tf->handle_http($t) == 0, 'Implicit HTTP/1.1 Keep-Alive');

ok($tf->stop_proc == 0, "Stopping lighttpd");
