#!/bin/bash
(shopt -s igncr) 2>/dev/null && shopt -s igncr; # comment is needed
#                                               # hack for cygwin bash
#                                               #  no-op for other
#
# Test various command line testable aspects of the Wireshark tools
#
# $Id: test.sh 32072 2010-03-01 22:53:15Z guy $
#
# Wireshark - Network traffic analyzer
# By Gerald Combs <gerald@wireshark.org>
# Copyright 2005 Ulf Lamping
#
# This program is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public License
# as published by the Free Software Foundation; either version 2
# of the License, or (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software
# Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
#

# an existing capture file
CAPFILE=./dhcp.pcap

PRINT_USAGE=0
USE_COLOR=0 
RUN_SUITE=all



shift $(( $OPTIND - 1 ))


##################### test-backend.sh ##########################################
#source ./test-backend.sh

# runtime flags
TEST_RUN="OFF"
TEST_OUTPUT="VERBOSE"	# "OFF", "DOTTED", "VERBOSE"

# runtime vars
TEST_NESTING_LEVEL=0	# nesting level of current test
TEST_STEPS[0]=0			# number of steps of a specific nesting level

# output counters
TEST_OK=0				# global count of succeeded steps
TEST_FAILED=0			# global count of failed steps
TEST_SKIPPED=0			# global count of failed steps

TEST_STEP_PRE_CB=
TEST_STEP_POST_CB=

# level number of this test item (suite or step)
test_level() {
  return
	LIMIT_LEVEL=100

	for ((a=0; a <= LIMIT_LEVEL ; a++))
	do
		if [ ! $a -eq 0 ]; then
			echo -n "."
		fi
		echo -n "${TEST_STEPS[a]}"
		if [ $a -eq $TEST_NESTING_LEVEL ]; then
			#echo "end"
			return
		fi
	done
}

# set output format
# $1 - "OUT", "DOTTED", "VERBOSE"
test_set_output() {
	TEST_OUTPUT=$1
}


test_suite_add() {
	$2
}

test_step_add() {

	#let "TEST_STEPS[$TEST_NESTING_LEVEL] += 1"
  TEST_STEP_NAME=$1
  #echo -n "TEST: " $1
  $TEST_STEP_PRE_CB
  $2
  $TEST_STEP_POST_CB
}


test_step_set_pre() {
	TEST_STEP_PRE_CB=$1
}
test_step_set_post() {
	TEST_STEP_POST_CB=$1
}


# the test step succeeded
test_step_ok() {
	# count appearance
  let "TEST_OK += 1"
  #echo -n ":result=0"

}

# the test step failed
# $1 output text
test_step_failed() {
	let "TEST_FAILED += 1"
	#echo  -n ":result=1"
	#echo "\"$TEST_STEP_NAME\" Failed!"
	#echo $1

}

test_step_skipped() {
	# count appearance
	let "TEST_SKIPPED += 1"
  echo " Skipped"
}

################################################################################

##################### config.sh ################################################
#source ./config.sh

if [ -n "${OS#Windows}" ] ; then
	WS_SYSTEM="Windows"
else
	WS_SYSTEM=`uname -s`
fi


# Path to the Wireshark binaries, only used for the settings below
WS_BIN_PATH=..

# Are we allowed to open interfaces or capture on this system?
SKIP_CAPTURE=0

# Override the last two items if we're running Windows
if [ "$WS_SYSTEM" = "Windows" ] ; then
	WS_BIN_PATH=../wireshark-gtk2
	SKIP_CAPTURE=0
fi

# Tweak the following to your liking.
WIRESHARK=$WS_BIN_PATH/wireshark
TSHARK=$WS_BIN_PATH/tshark
CAPINFOS=$WS_BIN_PATH/capinfos
DUMPCAP=$WS_BIN_PATH/dumpcap

if [ "$WS_SYSTEM" = "Windows" -a -z "$TRAFFIC_CAPTURE_IFACE" ] ; then
        # Try to fetch the first Ethernet interface.
        TRAFFIC_CAPTURE_IFACE=`$TSHARK -D 2>&1 | \
                egrep 'Ethernet|Network Connection|VMware' | \
                head -1 | cut -c 1`
fi
TRAFFIC_CAPTURE_IFACE=${TRAFFIC_CAPTURE_IFACE:-1}
TRAFFIC_CAPTURE_DURATION=60
TRAFFIC_CAPTURE_PROMISC=-p

if [ "$WS_SYSTEM" != "Windows" ] && which mkfifo &>/dev/null ; then
    TEST_FIFO=1
fi

################################################################################


##################### suite-clopts.sh ##########################################
#source ./suite-clopts.sh
EXIT_OK=0
EXIT_COMMAND_LINE=1
EXIT_ERROR=2

# generic: check against a specific exit status with a single char option
# $1 command: tshark
# $2 option: a
# $3 expected exit status: 0
test_single_char_options()
{

	#echo "command: "$1" opt1: "$2" opt2: "$3" opt3: "$4" opt4: "$5" opt5: "$6
	if [[ "$2" == "D" || "$2" == "L" ]]
	then
	    $1 -$2  > ./testout.txt 2>&1
	    RETURNVALUE=$?
	else
	    $1 -$2  > ./testout.txt 2>&1
	    RETURNVALUE=$?
	fi
	if [ ! $RETURNVALUE -eq $3 ]; then
		test_step_failed "exit status: $RETURNVALUE"
	else
		test_step_ok
	fi
	rm ./testout.txt
}


# check exit status when reading an existing file
clopts_step_existing_file() {
	$TSHARK -r $CAPFILE > ./testout.txt 2>&1
	RETURNVALUE=$?
	if [ ! $RETURNVALUE -eq $EXIT_OK ]; then
		test_step_failed "exit status: $RETURNVALUE"
	else
		test_step_ok
	fi
	rm ./testout.txt
}


# check exit status when reading a non-existing file
clopts_step_nonexisting_file() {
	$TSHARK -r ThisFileDontExist.pcap  > ./testout.txt 2>&1
	RETURNVALUE=$?
	if [ ! $RETURNVALUE -eq $EXIT_ERROR ]; then
		test_step_failed "exit status: $RETURNVALUE"
	else
		test_step_ok
	fi
	rm  ./testout.txt
}




# S V l n p q x


# check exit status and grep output string of an invalid interface
clopts_step_invalid_interface() {
	$TSHARK -i invalid_interface -w './testout.pcap' > ./testout.txt 2>&1
	RETURNVALUE=$?
	if [ ! $RETURNVALUE -eq $EXIT_COMMAND_LINE ]; then
		test_step_failed "exit status: $RETURNVALUE"
	else
		grep -i 'The capture session could not be initiated' ./testout.txt > /dev/null
		if [ $? -eq 0 ]; then
			test_step_ok
		else
			test_step_failed "Infos"
		fi
	fi
}

# check exit status and grep output string of an invalid interface index
# (valid interface indexes start with 1)
clopts_step_invalid_interface_index() {
	$TSHARK -i 0 -w './testout.pcap' > ./testout.txt 2>&1
	RETURNVALUE=$?
	if [ ! $RETURNVALUE -eq $EXIT_COMMAND_LINE ]; then
		test_step_failed "exit status: $RETURNVALUE"
	else
		grep -i 'there is no interface with that adapter index' ./testout.txt > /dev/null
		if [ $? -eq 0 ]; then
			test_step_ok
		else
			test_step_failed "Infos"
		fi
	fi
}



clopts_post_step() {
	rm -f ./testout.txt ./testout2.txt
}


################################################################################


##################### suite-io.sh ##############################################
#source ./suite-io.sh

EXIT_OK=0
EXIT_COMMAND_LINE=1
EXIT_ERROR=2


# input of file
io_step_input_file() {
	$DUT -r dhcp.pcap -w ./testout.pcap > ./testout.txt 2>&1
	RETURNVALUE=$?
	if [ ! $RETURNVALUE -eq $EXIT_OK ]; then
		test_step_failed "exit status of $DUT: $RETURNVALUE"
		# part of the Prerequisite checks
		# probably wrong interface, output the possible interfaces
		$TSHARK -D
		return
	fi

	# we should have an output file now
	if [ ! -f "./testout.pcap" ]; then
		test_step_failed "No output file!"
		return
	fi
	
	# ok, we got a capture file, does it contain exactly 10 packets?
	$CAPINFOS ./testout.pcap > ./testout.txt
	grep -Ei 'Number of packets:[[:blank:]]+4' ./testout.txt > /dev/null
	if [ $? -eq 0 ]; then
		test_step_ok
	else
		echo
		cat ./testout.txt
		# part of the Prerequisite checks
		# probably wrong interface, output the possible interfaces
		$TSHARK -D
		test_step_failed "No or not enough traffic captured. Probably the wrong interface: $TRAFFIC_CAPTURE_IFACE!"
	fi
}

# piping input file to stdout using "-w -" 
io_step_output_piping() {
	$DUT -r dhcp.pcap -w - > ./testout.pcap 2>./testout.txt
	RETURNVALUE=$?
	if [ ! $RETURNVALUE -eq $EXIT_OK ]; then
		test_step_failed "exit status of $DUT: $RETURNVALUE"
		$TSHARK -D
		return
	fi

	# we should have an output file now
	if [ ! -f "./testout.pcap" ]; then
		test_step_failed "No output file!"
		return
	fi
	
	# ok, we got a capture file, does it contain exactly 10 packets?
	$CAPINFOS ./testout.pcap > ./testout2.txt 2>&1
	grep -Ei 'Number of packets:[[:blank:]]+4' ./testout2.txt > /dev/null
	if [ $? -eq 0 ]; then
		test_step_ok
	else
		echo
		cat ./testout.txt
		cat ./testout2.txt
		$TSHARK -D
		test_step_failed "No or not enough traffic captured. Probably the wrong interface: $TRAFFIC_CAPTURE_IFACE!"
	fi
}

# piping input file to stdout using "-w -" 
io_step_input_piping() {
	cat -B dhcp.pcap | $DUT -r - -w ./testout.pcap 2>./testout.txt
	RETURNVALUE=$?
	if [ ! $RETURNVALUE -eq $EXIT_OK ]; then
		$TSHARK -D
		echo
		cat ./testout.txt
		test_step_failed "exit status of $DUT: $RETURNVALUE"
		return
	fi

	# we should have an output file now
	if [ ! -f "./testout.pcap" ]; then
		test_step_failed "No output file!"
		return
	fi
	
	# ok, we got a capture file, does it contain exactly 10 packets?
	$CAPINFOS ./testout.pcap > ./testout2.txt 2>&1
	grep -Ei 'Number of packets:[[:blank:]]+4' ./testout2.txt > /dev/null
	if [ $? -eq 0 ]; then
		test_step_ok
	else
		echo
		cat ./testout.txt
		cat ./testout2.txt
		$TSHARK -D
		test_step_failed "No or not enough traffic captured. Probably the wrong interface: $TRAFFIC_CAPTURE_IFACE!"
	fi
}

wireshark_io_suite() {
	# Q: quit after cap, k: start capture immediately
	DUT="$WIRESHARK"
	test_step_add "Input file" io_step_input_file
}

tshark_io_suite() {
	DUT=$TSHARK
	test_step_add "Input file" io_step_input_file
	test_step_add "Output piping" io_step_output_piping
	#test_step_add "Piping" io_step_input_piping
}

dumpcap_io_suite() {
	#DUT="$DUMPCAP -Q"
	DUT=$DUMPCAP
	
	test_step_add "Input file" io_step_input_file
}

io_cleanup_step() {
	rm -f ./testout.txt
	rm -f ./testout2.txt
	rm -f ./testout.pcap
	rm -f ./testout2.pcap
}


################################################################################


##################### suite-capture.sh #########################################
#source ./suite-capture.sh
EXIT_OK=0
EXIT_COMMAND_LINE=1
EXIT_ERROR=2

capture_out=./testout.pcap


capture_test_output_print() {
	wait
	for f in "$@"; do
		if [[ -f "$f" ]]; then
		printf " --> $f\n"
		cat "$f"
                printf "\n"
		fi
	done
}

traffic_gen_ping() {
	# Generate some traffic for quiet networks.
	# This will have to be adjusted for non-Windows systems.
	
	# the following will run in the background and return immediately
	{
	date
	for (( x=28; x<=58; x++ )) # in effect: number the packets
	do
		# How does ping _not_ have a standard set of arguments?
		case $WS_SYSTEM in
			Windows)
				ping -n 1 -l $x www.wireshark.org	;;
			SunOS)
				/usr/sbin/ping www.wireshark.org $x 1		;;
			*) # *BSD, Linux
				ping -c 1 -s $x www.wireshark.org	;;
		esac
		sleep 1
	done
	date
	} > ./testout_ping.txt 2>&1 &
}

ping_cleanup() {
	wait
	rm -f ./testout_ping.txt
}

# capture exactly 10 packets
capture_step_10packets() {
	if [ $SKIP_CAPTURE -ne 0 ] ; then
		test_step_skipped
		return
	fi

	traffic_gen_ping

	date > ./testout.txt
	$DUT -i $TRAFFIC_CAPTURE_IFACE $TRAFFIC_CAPTURE_PROMISC \
		-w $capture_out \
		-c 10  \
		-a duration:$TRAFFIC_CAPTURE_DURATION \
		-f icmp \
		>> ./testout.txt 2>&1
	RETURNVALUE=$?
	date >> ./testout.txt
	if [ ! $RETURNVALUE -eq $EXIT_OK ]; then
		echo
		capture_test_output_print ./testout.txt
		# part of the Prerequisite checks
		# wrong interface ? output the possible interfaces
		$TSHARK -D
		test_step_failed "exit status of $DUT: $RETURNVALUE"
		return
	fi

	# we should have an output file now
	if [ ! -f "$capture_out" ]; then
		capture_test_output ./testout.txt
		test_step_failed "No output file!"
		return
	fi

	# ok, we got a capture file, does it contain exactly 10 packets?
	$CAPINFOS $capture_out > ./testout2.txt
	grep -Ei 'Number of packets:[[:blank:]]+10' ./testout2.txt > /dev/null
	if [ $? -eq 0 ]; then
		test_step_ok
	else
		echo
                $TSHARK -ta -r $capture_out >> ./testout2.txt
		capture_test_output_print ./testout_ping.txt ./testout.txt ./testout2.txt
		# part of the Prerequisite checks
		# probably wrong interface, output the possible interfaces
		$TSHARK -D
		test_step_failed "No or not enough traffic captured. Probably the wrong interface: $TRAFFIC_CAPTURE_IFACE!"
	fi
}

# capture exactly 10 packets using "-w -" (piping to stdout)
capture_step_10packets_stdout() {
        if [ $SKIP_CAPTURE -ne 0 ] ; then
                test_step_skipped
                return
        fi

	traffic_gen_ping

	date > ./testout.txt
  $DUT -i $TRAFFIC_CAPTURE_IFACE $TRAFFIC_CAPTURE_PROMISC \
		-c 10 \
		-a duration:$TRAFFIC_CAPTURE_DURATION \
		-w - \
		-f icmp \
		> $capture_out 2>>./testout.txt
	RETURNVALUE=$?
	date >> ./testout.txt
	if [ ! $RETURNVALUE -eq $EXIT_OK ]; then
		echo
		cat ./testout.txt
		$TSHARK -D
		test_step_failed "exit status of $DUT: $RETURNVALUE"
		return
	fi

	# we should have an output file now
	if [ ! -f "$capture_out" ]; then
		test_step_failed "No output file!"
		return
	fi
	# ok, we got a capture file, does it contain exactly 10 packets?
	$CAPINFOS $capture_out > ./testout2.txt 2>&1
	grep -Ei 'Number of packets:[[:blank:]]+10' ./testout2.txt > /dev/null
	if [ $? -eq 0 ]; then
		test_step_ok
	else
		echo
		cat ./testout.txt
		cat ./testout2.txt
		$TSHARK -D
		test_step_failed "No or not enough traffic captured. Probably the wrong interface: $TRAFFIC_CAPTURE_IFACE!"
	fi
}

# capture packets via a fifo
capture_step_fifo() {
	mkfifo 'fifo'
	(cat $CAPFILE; sleep 1; tail -c +25 $CAPFILE) > fifo &
	$DUT -i fifo $TRAFFIC_CAPTURE_PROMISC \
		-w $capture_out \
		-a duration:$TRAFFIC_CAPTURE_DURATION \
		> ./testout.txt 2>&1
	RETURNVALUE=$?
	rm 'fifo'
	if [ ! $RETURNVALUE -eq $EXIT_OK ]; then
		test_step_failed "exit status of $DUT: $RETURNVALUE"
		return
	fi

	# we should have an output file now
	if [ ! -f "$capture_out" ]; then
		test_step_failed "No output file!"
		return
	fi

	# ok, we got a capture file, does it contain exactly 8 packets?
	$CAPINFOS $capture_out > ./testout.txt
	grep -Ei 'Number of packets:[[:blank:]]+8' ./testout.txt > /dev/null
	if [ $? -eq 0 ]; then
		test_step_ok
	else
		echo
		cat ./testout.txt
		test_step_failed "No or not enough traffic captured."
	fi
}

# capture exactly 2 times 10 packets (multiple files)
capture_step_2multi_10packets() {
        if [ $SKIP_CAPTURE -ne 0 ] ; then
                test_step_skipped
                return
        fi

	traffic_gen_ping

	date > ./testout.txt
	$DUT -i $TRAFFIC_CAPTURE_IFACE $TRAFFIC_CAPTURE_PROMISC \
		-w $capture_out \
		-c 10 \
		-a duration:$TRAFFIC_CAPTURE_DURATION \
		-f icmp \
		>> ./testout.txt 2>&1

	RETURNVALUE=$?
	date >> ./testout.txt
	if [ ! $RETURNVALUE -eq $EXIT_OK ]; then
		echo
		cat ./testout.txt
		# part of the Prerequisite checks
		# probably wrong interface, output the possible interfaces
		$TSHARK -D
		test_step_failed "exit status of $DUT: $RETURNVALUE"
		return
	fi

	# we should have an output file now
	if [ ! -f "$capture_out" ]; then
		test_step_failed "No output file!"
		return
	fi

	# ok, we got a capture file, does it contain exactly 10 packets?
	$CAPINFOS $capture_out > ./testout.txt
	grep -Ei 'Number of packets:[[:blank:]]+10' ./testout.txt > /dev/null
	if [ $? -eq 0 ]; then
		test_step_ok
	else
		echo
		cat ./testout.txt
		test_step_failed "Probably the wrong interface (no traffic captured)!"
	fi
}

# capture with a very unlikely read filter, packets must be zero afterwards
capture_step_read_filter() {
        if [ $SKIP_CAPTURE -ne 0 ] ; then
                test_step_skipped
                return
        fi

	traffic_gen_ping

	# valid, but very unlikely filter
	date > ./testout.txt
	$DUT -i $TRAFFIC_CAPTURE_IFACE $TRAFFIC_CAPTURE_PROMISC \
		-w $capture_out \
		-a duration:$TRAFFIC_CAPTURE_DURATION \
		-R 'dcerpc.cn_call_id==123456' \
		-c 10 \
		-f icmp \
		>> ./testout.txt 2>&1
	RETURNVALUE=$?
	date >> ./testout.txt
	if [ ! $RETURNVALUE -eq $EXIT_OK ]; then
		echo
		cat ./testout.txt
		# part of the Prerequisite checks
		# wrong interface ? output the possible interfaces
		$TSHARK -D
		test_step_failed "exit status: $RETURNVALUE"
		return
	fi

	# we should have an output file now
	if [ ! -f "$capture_out" ]; then
		test_step_failed "No output file!"
		return
	fi

	# ok, we got a capture file, does it contain exactly 0 packets?
	$CAPINFOS $capture_out > ./testout.txt
	grep -Ei 'Number of packets:[[:blank:]]+0' ./testout.txt > /dev/null
	if [ $? -eq 0 ]; then
		test_step_ok
	else
		echo
		cat ./testout.txt
		test_step_failed "Capture file should contain zero packets!"
	fi
}


# capture with a snapshot length
capture_step_snapshot() {
        if [ $SKIP_CAPTURE -ne 0 ] ; then
                test_step_skipped
                return
        fi

	traffic_gen_ping

	# capture with a snapshot length of 68 bytes for $TRAFFIC_CAPTURE_DURATION seconds
	# this should result in no packets greater than 68 bytes
	#date > ./testout.txt
	$DUT -i $TRAFFIC_CAPTURE_IFACE $TRAFFIC_CAPTURE_PROMISC \
		-w $capture_out \
		-s 68 \
		-a duration:$TRAFFIC_CAPTURE_DURATION \
		-f icmp \
		>> ./testout.txt 2>&1
	RETURNVALUE=$?
	#date >> ./testout.txt
	if [ ! $RETURNVALUE -eq $EXIT_OK ]; then
		echo
		cat ./testout.txt
		# part of the Prerequisite checks
		# wrong interface ? output the possible interfaces
		$TSHARK -D
		test_step_failed "exit status: $RETURNVALUE"
		return
	fi

	# we should have an output file now
	if [ ! -f "$capture_out" ]; then
		test_step_failed "No output file!"
		return
	fi
	# use tshark to filter out all packets, which are larger than 68 bytes
	$TSHARK -r $capture_out -w ./testout2.pcap -R 'frame.cap_len>68' > ./testout.txt 2>&1

	# ok, we got a capture file, does it contain exactly 0 packets?
	$CAPINFOS ./testout2.pcap > ./testout.txt
	grep -Ei 'Number of packets:[[:blank:]]+0' ./testout.txt > /dev/null
	if [ $? -eq 0 ]; then
		test_step_ok
	else
		echo
		cat ./testout.txt
		test_step_failed "Capture file should contain zero packets!"
		return
	fi
}



capture_cleanup_step() {
	ping_cleanup
	rm -f ./testout.txt
	rm -f ./testout2.txt
	rm -f ./testout.pcap
	rm -f ./testout2.pcap
}

################################################################################


##################### suite-unittests.sh #######################################
#source ./suite-unittests.sh
if [ "$WS_SYSTEM" == "Windows" ] ; then
	MAKE="nmake -f Makefile.nmake"
else
	MAKE=make
fi

unittests_step_test() {
	#( cd `dirname $DUT` && $MAKE `basename $DUT` ) >testout.txt 2>&1
	#mkd5m might be wackiness here, is make clean needed?
	# cd `dirname $DUT` && make  &> /dev/null `basename $DUT`
	#if [ $? -ne 0 ]; then
	#	echo
	#	cat ./testout.txt
	#	test_step_failed "make $DUT failed"
	#	return
	#fi

    # if we're on windows, we have to copy the test exe to the wireshark-gtk2
    # dir before we can use them.
    # {Note that 'INSTALL_DIR' must be a Windows Pathname)
	#if [ "$WS_SYSTEM" == "Windows" ] ; then
	#	(cd `dirname $DUT` && $MAKE `basename $DUT`_install INSTALL_DIR='..\wireshark-gtk2') > testout.txt 2>&1
	#	if [ $? -ne 0 ]; then 
	#		echo
	#		cat ./testout.txt
	#		test_step_failed "install $DUT failed"
	#		return
	#	fi
	#	DUT=../wireshark-gtk2/`basename $DUT`
	#fi

	$DUT > testout.txt 2>&1
	RETURNVALUE=$?
	if [ ! $RETURNVALUE -eq $EXIT_OK ]; then
		echo
		cat ./testout.txt
		test_step_failed "exit status of $DUT: $RETURNVALUE"
		return
	fi
	test_step_ok
}


unittests_step_exntest() {
	DUT=../epan/exntest
	unittests_step_test
}

unittests_step_reassemble_test() {
	DUT=../epan/reassemble_test
	unittests_step_test
}

unittests_step_tvbtest() {
	DUT=../epan/tvbtest
	unittests_step_test
}

unittests_cleanup_step() {
	rm -f ./testout.txt
}


################################################################################
#check prerequisites
test_step_prerequisites() {

  NOTFOUND=0
  for i in "$WIRESHARK" "$TSHARK" "$CAPINFOS" "$DUMPCAP" ; do
    if [ ! -x $i ]; then
      echo "Couldn't find $i"
      NOTFOUND=1
    fi
  done
  if [ $NOTFOUND -eq 1 ]; then
    test_step_failed "Tool not found"
  else
    test_step_ok
  fi
}


NUM=$(( $1 - 1 ))


cd test
#test_set_output VERBOSE
noop () { : ; }
TEST_RUN="ON"

mkd5m_setup () {
rm -f ./testout.pcap 
touch ./testout.pcap 
chown root:root ./testout.pcap
}
# clopts suite
if [[ $NUM -le 46 ]]
then
    test_step_set_pre noop
    test_step_set_post clopts_post_step
    if [[ $NUM -le 37 ]]
    then
        invalid=( A B C E F H J K M N O Q R T U W X Y Z a b c d e f g i j k m o r s t u w y z )
        letter=${invalid[$NUM]}
        test_step_add "invalid option: $letter  " "test_single_char_options $TSHARK $letter 1"
    elif [[ $NUM -le 40 ]]
    then
        valid=(G h v)
        index=$(( $NUM - 38 ))
        letter=${valid[$index]}
        test_step_add "valid option -$letter" "test_single_char_options $TSHARK $letter 0"
    elif [[ $NUM -le 42 ]]
    then
        if [[ $NUM -eq 41 ]]
        then letter=D
        else letter=L
        fi
        test_step_add "valid interface opt -$letter" "test_single_char_options $TSHARK $letter 0"
    else
        case $NUM in
            43) test_step_add "Exit status for existing file: \""$CAPFILE"\" must be 0"  clopts_step_existing_file ;;
            44) test_step_add "Exit status for none existing files must be 2" clopts_step_nonexisting_file ;;
            45) test_step_add  "Invalid capture interface -i" clopts_step_invalid_interface ;;
            46) test_step_add  "Invalid capture interface index 0"  clopts_step_invalid_interface_index ;;
        esac
    fi
    
#preprequisites suite
elif [[ $NUM -eq 47 ]]
then
    test_step_set_pre noop
    test_step_set_post noop
    test_step_add "Prerequisites settings" test_step_prerequisites

#io_suite
elif [[ $NUM -le 49 ]]
then
  test_step_set_pre io_cleanup_step
  test_step_set_post io_cleanup_step
  DUT=$TSHARK
  case $NUM in
      48) test_step_add "Input file" io_step_input_file ;;
      49) test_step_add "Output piping" io_step_output_piping ;;
  esac

#capture_suite
elif [[ $NUM -le 57 ]]
then
    #test_step_set_pre capture_cleanup_step
    #test_step_set_post capture_cleanup_step
    #capture_cleanup_step
    #ping_cleanup 
    
    
    #I know the DUT=stuff is redundant but its safest this way (and not any slower)
    case $NUM in
        50) DUT=$DUMPCAP 
            test_step_set_pre ping_cleanup
            test_step_set_post capture_cleanup_step
            mkd5m_setup 
            test_step_add "dumpcap cap 10" capture_step_10packets ;;
        51) DUT=$TSHARK 
            test_step_set_pre ping_cleanup
            test_step_set_post capture_cleanup_step
            mkd5m_setup 
            test_step_add "tshark cap 10" capture_step_10packets ;;
        52) DUT=$DUMPCAP 
            test_step_set_pre capture_cleanup_step
            test_step_set_post capture_cleanup_step
            mkd5m_setup 
            test_step_add "dumpcap cap 10 stdout" capture_step_10packets_stdout ;;
        53) DUT=$TSHARK 
            test_step_set_pre capture_cleanup_step
            test_step_set_post capture_cleanup_step
            mkd5m_setup 
            test_step_add "tshark cap 10 stdout" capture_step_10packets_stdout ;;
        54) DUT=$DUMPCAP 
            test_step_set_pre capture_cleanup_step
            test_step_set_post capture_cleanup_step
            test_step_add "dumpcap cap fifo" capture_step_fifo ;;
        55) DUT=$TSHARK 
            test_step_set_pre capture_cleanup_step
            test_step_set_post capture_cleanup_step
            test_step_add "tshark cap fifo" capture_step_fifo ;;
        56) DUT=$DUMPCAP 
            test_step_set_pre ping_cleanup
            test_step_set_post capture_cleanup_step
            mkd5m_setup 
            test_step_add "dumpcap 68 byte snapshot" capture_step_snapshot ;;
        57) DUT=$TSHARK 
            test_step_set_pre ping_cleanup
            test_step_set_post capture_cleanup_step
            mkd5m_setup 
            test_step_add "tshark 68 byte snapshot" capture_step_snapshot ;;
        #test_step_add "Capture read filter (${TRAFFIC_CAPTURE_DURATION}s)" capture_step_read_filter
    esac
#unit tests
else
    test_step_set_pre unittests_cleanup_step
    test_step_set_post unittests_cleanup_step
    case $NUM in
        58) test_step_add "exntest" unittests_step_exntest ;; 
        59) test_step_add "reassemble_test" unittests_step_reassemble_test ;;
        60) test_step_add "tvbtest" unittests_step_tvbtest ;;
    esac
fi
if [[ $TEST_OK -eq 1 ]]
then 
    echo -e "PASS: \t$NUM  $TEST_STEP_NAME" 1>&2
    exit 0
elif [[ $TEST_OK -eq 0 ]]
then
    echo -e "FAIL: \t$NUM  $TEST_STEP_NAME" 1>&2
    exit 1
else
    echo "More than one test was run??" 1>&2
    exit 255
fi



