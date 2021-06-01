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
GET /server-status HTTP/1.0
User-Agent: Wget/1.9.1
Authorization: Digest username="jan", realm="jan",
	nonce="b1d12348b4620437c43dd61c50ae4639",
	uri="/MJ-BONG.xm.mpc", qop=auth, noncecount=00000001",
	cnonce="036FCA5B86F7E7C4965C7F9B8FE714B7",
	response="29B32C2953C763C6D033C8A49983B87E"
EOF
 );
$t->{RESPONSE} = [ { 'HTTP-Protocol' => 'HTTP/1.0', 'HTTP-Status' => 400 } ];
ok($tf->handle_http($t) == 0, 'Digest-Auth: missing nc (noncecount instead), no crash');

ok($tf->stop_proc == 0, "Stopping lighttpd");
