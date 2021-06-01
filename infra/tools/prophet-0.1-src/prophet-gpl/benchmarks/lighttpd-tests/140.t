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
Accept-Encoding: gzip, deflate
EOF
 );
$t->{RESPONSE} = [ { 'HTTP-Protocol' => 'HTTP/1.0', 'HTTP-Status' => 200, '+Vary' => '', '+Content-Encoding' => '' } ];
ok($tf->handle_http($t) == 0, 'gzip, deflate - Content-Length and Content-Encoding is set');

ok($tf->stop_proc == 0, "Stopping lighttpd");
