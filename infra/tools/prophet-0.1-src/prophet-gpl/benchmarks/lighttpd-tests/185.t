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
OPTIONS rtsp://221.192.134.146:80 RTSP/1.1
Host: 221.192.134.146:80
EOF
 );
$t->{RESPONSE} = [ { 'HTTP-Protocol' => 'HTTP/1.0', 'HTTP-Status' => 505 } ];
ok($tf->handle_http($t) == 0, 'OPTIONS for RTSP');

ok($tf->stop_proc == 0, "Stopping lighttpd");
