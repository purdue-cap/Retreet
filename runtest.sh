#!/bin/bash

fuse="fuse"
parallel="parallel"
testpath="case_study/"
sizecounting=${testpath}"size_counting/"
css=${testpath}"css/"
shiftsum=${testpath}"shiftsum/"
cycletree=${testpath}"cycletree/"
retreet=".retreet"
mona=".mona"
output="output/"

if [ "$1" = $fuse ]
then
	if [ "$2" = "size_counting_fusible" ]
	then
		./exec.sh $fuse ${sizecounting}$2${retreet} ${sizecounting}"fusible_size_counting_fused"${retreet} ${sizecounting}"fusible_size_counting_relation"${retreet}
	fi
	if [ "$2" = "size_counting_infusible" ]
	then
		./exec.sh $fuse ${sizecounting}$2${retreet} ${sizecounting}"infusible_size_counting_fused"${retreet} ${sizecounting}"infusible_size_counting_relation"${retreet}
	fi
	if [ "$2" = "shiftsum" ]
	then
		./exec.sh $fuse ${shiftsum}$2${retreet} ${shiftsum}"fusible_shiftsum_fused"${retreet} ${shiftsum}"fusible_shiftsum_relation"${retreet}
	fi
	if [ "$2" = "css" ]
	then
		./exec.sh $fuse ${css}$2${retreet} ${css}"fusible_css_fused"${retreet} ${css}"fusible_css_relation"${retreet}
	fi
	if [ "$2" = "cycletree" ]
	then
		./exec.sh $fuse ${cycletree}$2${retreet} ${cycletree}"fusible_cycletree_fused"${retreet} ${cycletree}"fusible_cycletree_relation"${retreet}
		echo "Generated mona file."
		echo ""
		echo "Checking "${fuse}"_"$2"_1"${mona}" ..."
		echo ""
		mona ${output}${fuse}"_"$2"_1"${mona}
		echo ""
		echo "Checking "${fuse}"_"$2"_2"${mona}" ..."
		echo ""
		mona ${output}${fuse}"_"$2"_2"${mona}
		echo ""
		echo "Checking "${fuse}"_"$2"_3"${mona}" ..."
		echo ""
		mona ${output}${fuse}"_"$2"_3"${mona}
		echo ""
		echo "Checking "${fuse}"_"$2"_4"${mona}" ..."
		echo ""
		mona ${output}${fuse}"_"$2"_4"${mona}
		echo ""
		echo "Checking "${fuse}"_"$2"_5"${mona}" ..."
		echo ""
		mona ${output}${fuse}"_"$2"_5"${mona}
	fi
	if [ "$2" != "cycletree" ]
	then
		echo "Generated mona file."
		echo ""
		echo "Checking "${fuse}"_"$2${mona}" ..."
		echo ""
		mona ${output}${fuse}"_"$2${mona}
	fi
fi
if [ "$1" = $parallel ]
then
	if [ "$2" = "size_counting" ]
	then
		./exec.sh $parallel ${sizecounting}$2"_parallel"${retreet}
	fi
	if [ "$2" = "cycletree" ]
	then
		./exec.sh $parallel ${cycletree}$2"_parallel"${retreet}
	fi
	echo "Generated mona file."
	echo ""
	echo "Checking "$2"_"${parallel}${mona}" ..."
	echo ""
	mona ${output}$2"_"${parallel}${mona}
fi
echo "done"
