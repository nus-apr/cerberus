#!/usr/bin/env perl
BEGIN {
	# add current source dir to the include-path
	# we need this for make distcheck
	(my $srcdir = $0) =~ s,/[^/]+$,/,;
	unshift @INC, $srcdir;
}

use strict;
use IO::Socket;
use Test::More tests => 21;
use LightyTest;

my $tf_proxy = LightyTest->new();
my $tf_backend1 = LightyTest->new();
my $tf_backend2 = LightyTest->new();

my $t;

## we need two procs
## 1. the real webserver
## 2. the proxy server

SKIP: {
  skip "disabled for now", 21;
$tf_proxy->{PORT} = 2048;
$tf_proxy->{CONFIGFILE} = 'proxy.conf';
$tf_proxy->{LIGHTTPD_PIDFILE} = $tf_proxy->{SRCDIR}.'/tmp/lighttpd/lighttpd-proxy.pid';

$tf_backend1->{PORT} = 2050;
$tf_backend1->{CONFIGFILE} = 'proxy-backend-1.conf';
$tf_backend1->{LIGHTTPD_PIDFILE} = $tf_backend1->{SRCDIR}.'/tmp/lighttpd/lighttpd-backend-1.pid';

$tf_backend2->{PORT} = 2051;
$tf_backend2->{CONFIGFILE} = 'proxy-backend-2.conf';
$tf_backend2->{LIGHTTPD_PIDFILE} = $tf_backend2->{SRCDIR}.'/tmp/lighttpd/lighttpd-backend-2.pid';


ok($tf_backend1->start_proc == 0, "Starting lighttpd") or die();

ok($tf_proxy->start_proc == 0, "Starting lighttpd as proxy") or die();

sleep(1);

$t->{REQUEST}  = ( <<EOF
GET /index.html HTTP/1.0
Host: www.example.org
EOF
 );
$t->{RESPONSE} = [ { 'HTTP-Protocol' => 'HTTP/1.0', 'HTTP-Status' => 200 } ];
ok($tf_proxy->handle_http($t) == 0, 'valid request');

$t->{REQUEST}  = ( <<EOF
GET /index.html HTTP/1.0
Host: www.example.org
EOF
 );
$t->{RESPONSE} = [ { 'HTTP-Protocol' => 'HTTP/1.0', 'HTTP-Status' => 200, 'Server' => 'proxy-backend-1' } ];
ok($tf_proxy->handle_http($t) == 0, 'drop Server from real server');

$t->{REQUEST}  = ( <<EOF
GET /balance-rr/foo HTTP/1.0
Host: www.example.org
EOF
 );
$t->{RESPONSE} = [ { 'HTTP-Protocol' => 'HTTP/1.0', 'HTTP-Status' => 404, 'Server' => 'proxy-backend-1' } ];
ok($tf_proxy->handle_http($t) == 0, 'balance rr - one backend');

$t->{REQUEST}  = ( <<EOF
GET /balance-rr/foo HTTP/1.0
Host: www.example.org
EOF
 );
$t->{RESPONSE} = [ { 'HTTP-Protocol' => 'HTTP/1.0', 'HTTP-Status' => 404, 'Server' => 'proxy-backend-1' } ];
ok($tf_proxy->handle_http($t) == 0, 'balance rr - one host down, failover');

$t->{REQUEST}  = ( <<EOF
GET /balance-fair/foo HTTP/1.0
Host: www.example.org
EOF
 );
$t->{RESPONSE} = [ { 'HTTP-Protocol' => 'HTTP/1.0', 'HTTP-Status' => 404, 'Server' => 'proxy-backend-1' } ];
ok($tf_proxy->handle_http($t) == 0, 'balance fair - one backend');

## backend 2 starting 
ok($tf_backend2->start_proc == 0, "Starting second proxy backend") or die();

$t->{REQUEST}  = ( <<EOF
GET /balance-rr/foo HTTP/1.0
Host: www.example.org
EOF
 );
$t->{RESPONSE} = [ { 'HTTP-Protocol' => 'HTTP/1.0', 'HTTP-Status' => 404, 'Server' => 'proxy-backend-2' } ];
ok($tf_proxy->handle_http($t) == 0, 'balance rr - lb, backend 1');

$t->{REQUEST}  = ( <<EOF
GET /balance-rr/foo HTTP/1.0
Host: www.example.org
EOF
 );
$t->{RESPONSE} = [ { 'HTTP-Protocol' => 'HTTP/1.0', 'HTTP-Status' => 404, 'Server' => 'proxy-backend-1' } ];
ok($tf_proxy->handle_http($t) == 0, 'balance rr - lb, backend 2');

$t->{REQUEST}  = ( <<EOF
GET /balance-hash/foo HTTP/1.0
Host: www.example.org
EOF
 );
$t->{RESPONSE} = [ { 'HTTP-Protocol' => 'HTTP/1.0', 'HTTP-Status' => 404, 'Server' => 'proxy-backend-1' } ];
ok($tf_proxy->handle_http($t) == 0, 'balance hash - lb, backend 1');

$t->{REQUEST}  = ( <<EOF
GET /balance-hash/foo HTTP/1.0
Host: www.example.org
EOF
 );
$t->{RESPONSE} = [ { 'HTTP-Protocol' => 'HTTP/1.0', 'HTTP-Status' => 404, 'Server' => 'proxy-backend-1' } ];
ok($tf_proxy->handle_http($t) == 0, 'balance hash - lb, backend 1 - same URL');

$t->{REQUEST}  = ( <<EOF
GET /balance-hash/bar HTTP/1.0
Host: www.example.org
EOF
 );
$t->{RESPONSE} = [ { 'HTTP-Protocol' => 'HTTP/1.0', 'HTTP-Status' => 404, 'Server' => 'proxy-backend-2' } ];
ok($tf_proxy->handle_http($t) == 0, 'balance hash - lb, backend 2');

$t->{REQUEST}  = ( <<EOF
GET /balance-hash/bar HTTP/1.0
Host: www.example.org
EOF
 );
$t->{RESPONSE} = [ { 'HTTP-Protocol' => 'HTTP/1.0', 'HTTP-Status' => 404, 'Server' => 'proxy-backend-2' } ];
ok($tf_proxy->handle_http($t) == 0, 'balance hash - lb, backend 2 - same URL');

## backend 1 stopping, failover 
ok($tf_backend1->stop_proc == 0, "Stopping backend 1");

$t->{REQUEST}  = ( <<EOF
GET /balance-hash/foo HTTP/1.0
Host: www.example.org
EOF
 );
$t->{RESPONSE} = [ { 'HTTP-Protocol' => 'HTTP/1.0', 'HTTP-Status' => 404, 'Server' => 'proxy-backend-2' } ];
ok($tf_proxy->handle_http($t) == 0, 'balance hash - failover to backend 2');

$t->{REQUEST}  = ( <<EOF
GET /balance-hash/bar HTTP/1.0
Host: www.example.org
EOF
 );
$t->{RESPONSE} = [ { 'HTTP-Protocol' => 'HTTP/1.0', 'HTTP-Status' => 404, 'Server' => 'proxy-backend-2' } ];
ok($tf_proxy->handle_http($t) == 0, 'balance hash - failover to backend 2 - same URL');

$t->{REQUEST}  = ( <<EOF
GET /balance-rr/foo HTTP/1.0
Host: www.example.org
EOF
 );
$t->{RESPONSE} = [ { 'HTTP-Protocol' => 'HTTP/1.0', 'HTTP-Status' => 404, 'Server' => 'proxy-backend-2' } ];
ok($tf_proxy->handle_http($t) == 0, 'balance rr - failover to backend 2');

$t->{REQUEST}  = ( <<EOF
GET /balance-fair/foo HTTP/1.0
Host: www.example.org
EOF
 );
$t->{RESPONSE} = [ { 'HTTP-Protocol' => 'HTTP/1.0', 'HTTP-Status' => 404, 'Server' => 'proxy-backend-2' } ];
ok($tf_proxy->handle_http($t) == 0, 'balance fair - failover to backend 2');


ok($tf_backend2->stop_proc == 0, "Stopping lighttpd");

ok($tf_proxy->stop_proc == 0, "Stopping lighttpd proxy");
}
