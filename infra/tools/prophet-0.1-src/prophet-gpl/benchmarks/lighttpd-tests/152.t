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
use Digest::MD5 qw(md5_hex);

my $tf = LightyTest->new();
my $t;

my $secret = "verysecret";
my $f = "/index.html";
my $thex = sprintf("%08x", time);
my $m = md5_hex($secret.$f.$thex);


$thex = sprintf("%08x", time - 1800);
$m = md5_hex($secret.$f.$thex);

ok($tf->start_proc == 0, "Starting lighttpd") or die();
$t->{REQUEST}  = ( <<EOF
GET /sec/$m/$thex$f HTTP/1.0
Host: vvv.example.org
EOF
 );
$t->{RESPONSE} = [ { 'HTTP-Protocol' => 'HTTP/1.0', 'HTTP-Status' => 410 } ];

ok($tf->handle_http($t) == 0, 'secdownload - timeout');

ok($tf->stop_proc == 0, "Stopping lighttpd");
