#!/bin/bash

for i in `ls *libtiff*.tar.gz`; do 
	subject=${i/.tar.gz/}
	echo $subject
	if [ ! -d $subject ]; then
		tar -xzvf $i > /dev/null;
	fi
	if [ -d $subject ]; then
		cd $subject;
		grep "plausible patches" ./original.txt
		grep "search space size" ./original.txt
		grep "reduced num plausible patch" *-output.log | tail -1
		cd - > /dev/null;
	fi
done


