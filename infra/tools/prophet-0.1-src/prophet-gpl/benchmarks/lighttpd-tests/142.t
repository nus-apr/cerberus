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

$tf->{CONFIGFILE} = 'mod-compress.conf';
ok($tf->start_proc == 0, "Starting lighttpd") or die();
$t->{REQUEST}  = ( <<EOF
GET /index.txt HTTP/1.0
Accept-encoding:
X-Accept-encoding: x-i2p-gzip;q=1.0, identity;q=0.5, deflate;q=0, gzip;q=0, *;q=0
User-Agent: MYOB/6.66 (AN/ON)
Connection: close
EOF
 );
$t->{RESPONSE} = [ { 'HTTP-Protocol' => 'HTTP/1.0', 'HTTP-Status' => 200, '+Vary' => '', 'Content-Type' => "text/plain" } ];
ok($tf->handle_http($t) == 0, 'Empty Accept-Encoding');

ok($tf->stop_proc == 0, "Stopping lighttpd");
