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
HEAD / HTTP/1.0
EOF
 );
$t->{RESPONSE} = [ { 'HTTP-Protocol' => 'HTTP/1.0', 'HTTP-Status' => 200, '-HTTP-Content' => ''} ];
ok($tf->handle_http($t) == 0, 'HEAD request, no content');

ok($tf->stop_proc == 0, "Stopping lighttpd");
