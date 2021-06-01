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
Range: bytes=0-1,3-4
EOF
 );
$t->{RESPONSE} = [ { 'HTTP-Protocol' => 'HTTP/1.0', 'HTTP-Status' => 206, 'HTTP-Content' => <<EOF
\r
--fkj49sn38dcn3\r
Content-Range: bytes 0-1/6\r
Content-Type: text/plain\r
\r
12\r
--fkj49sn38dcn3\r
Content-Range: bytes 3-4/6\r
Content-Type: text/plain\r
\r
45\r
--fkj49sn38dcn3--\r
EOF
 } ];
ok($tf->handle_http($t) == 0, 'GET, Range 0-1,3-4');

ok($tf->stop_proc == 0, "Stopping lighttpd");
