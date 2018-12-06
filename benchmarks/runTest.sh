#!/bin/sh
file=$1
#echo $file
while read option ;
do
        #echo $file
	../sim-outorder-nuca $option cc1.alpha -O 1stmt.i &> cc1_"$option".txt
	../sim-outorder-nuca $option go.alpha 50 9 2stone9.in > OUT &> go_"$option".txt
	../sim-outorder-nuca $option anagram.alpha words < anagram.in > OUT &> anagram_"$option".txt
        #echo ----------------------------------------------------------------------------\n
done < "$file"

