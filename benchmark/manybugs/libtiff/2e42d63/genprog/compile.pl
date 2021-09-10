#!/usr/bin/perl -w
use strict ;
use File::Basename ;

#flatten the path
$ARGV[0]  =~ s/\/[.]\//\//g ;
my $subdir = basename(dirname($ARGV[0])) ;
my $project = "/experiment/manybugs/libtiff/2e42d63/src" ;
my $project_list = "bugged-program.txt" ;


sub say {
    my $msg = $_[0];
    print STDERR "|[$0]|: $msg \n" ;
}
sub execute
{
    my $cmd = $_[0] ;
    my $res = system($cmd) >> 8 ;
    if ($res != 0)
    {
        print STDERR "Command '$cmd' failed: $!" ;

    }
}
sub make
{
    my $is_php = ($project =~ "php");
    if ($is_php)
    {
        system("rm ./sapi/cli/php");
    }
    my $res = system("make 2>&1") >> 8 ;
    # Python is picky when it comes to coverage instrumentation
    if ($res != 0 && ($project =~ m/python/) && ($subdir =~ m/coverage/))
    {
        say "FAILED TO COMPILE PYTHON" ;
        say "TRYING AGAIN, THIS MIGHT TAKE AWHILE!" ;
        my $result = system("make clean 2>&1") >> 8 ;
        if ($result != 0)
        {
            my $remake = system("make 2>&1") >> 8 ;
            if ($remake != 0) { say "DIDNT WORK, DYING" ; exit 1 ; }
            else { say "WORKED!" ; exit 0; }
        }
        else
        {
            say "Failed to make clean, dying";
            exit 1;
        }

    }
    elsif ($res == 0)
    {
        exit 0;
    }
    if ($is_php && $res != 0)
    {
        if (-f "./sapi/cli/php")
        {
            exit 0;
        }
    }
    exit 1;
}
# We want to change /home/mkd5m/genprog-many-bugs/libtiff-A-B/sanity/repair.sanity.c into sanity

my $do_coverage = ($subdir =~ m/coverage/) ;
open(FILE, "<$project_list") ;
my @repair_only = <FILE> ;
chomp @repair_only ;
my %pfiles= map { $_, 1 } @repair_only ;
close(FILE) ;
my @all = () ;

foreach my $file (grep (! m/coverage[.]path/, `find $subdir`))
{
    chomp $file ;
    if (-f $file && ! ($file =~ m/coverage[.]path/))
    {
        $file =~ s/^[^\/]*\/// ;
        push(@all, $file) ;
    }
}
my @coverage_only = () ;
foreach my $file (@all)
{
    chomp $file ;
    if (! exists($pfiles{$file}))
    {
        push(@coverage_only, $file)
    }
}
print "Coverage only: @coverage_only\n" ;
print "Repair files: @repair_only\n" ;
print "Allfiles: @all\n" ;
foreach my $file (@coverage_only)
{
    print "mv $project/$file $project/$file-temp\n" ;
    execute("mv $project/$file $project/$file-temp") ;

}
my @to_copy = $do_coverage? @all : @repair_only ;

foreach my $file(@to_copy)
{

   (-f "$subdir/$file") or die "Invalid file to copy: $subdir/$file" ;
   execute("cp $subdir/$file $file") ;
   execute("sed -i '/booo/d' $file");
}
chdir $project or die "fail chdir $project: $!" ;
make () ;
chdir ".." or die "failed chdir ..: $!" ;
foreach my $file (@coverage_only)
{
    print "mv $project/$file-temp $project/$file\n" ;
    execute("mv $project/$file-temp $file") ;

}


