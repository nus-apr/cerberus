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

$tf->{CONFIGFILE} = 'lighttpd.conf';
ok($tf->start_proc == 0, "Starting lighttpd") or die();
$t->{REQUEST} = ( <<EOF
GET /nofile HTTP/1.1
Host: bug255.example.org

GET /nofile HTTP/1.1
Host: bug255.example.org
Connection: close
EOF
 );
$t->{RESPONSE} = [ { 'HTTP-Protocol' => 'HTTP/1.1', 'HTTP-Status' => 403 },  { 'HTTP-Protocol' => 'HTTP/1.1', 'HTTP-Status' => 403 } ];
ok($tf->handle_http($t) == 0, 'remote ip cache (#255)');

ok($tf->stop_proc == 0, "Stopping lighttpd");
