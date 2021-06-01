#!/usr/bin/perl 

my $status = 200;

if (defined $ENV{"QUERY_STRING"}) {
	$status = $ENV{"QUERY_STRING"};
}

if ($status == 0 && $status ne "0") {
	# not a number, just send as content
	print $status;
} else {
	print "HTTP/1.0 ".$status." FooBar\r\n\r\n";
}
