
#build decs2.txt built/decs.txt

inputfile=$1 

files="$(cut -d' ' -f1 $inputfile | sort -u )"

inc=1

moddate() {
out="$( stat -f '%m' $1  2> /dev/null)"
if [[ "$?" != "0" ]] ;then 
out=$[inc + 1]
inc=$out;
fi
#echo "moddate $1 $out"
}

rm -f decs2.txt
rm -f built/decs.txt
echo "start" >> built/decs.txt
for pp in $files ; do
	grep "^$pp " $inputfile >"tmp/3$pp"
	grep "^$pp parts="  "tmp/3$pp"  > "tmp/2$pp"
	prefix=
	suffix=
	parts=
	for p in $(cut -d" " -f3- "tmp/2$pp") 
	do
		if [[ ${p::1} == "." ]]
		then
		if [[ ${p::2} == "./" ]]; then 
		prefix="${p:2}"
		else suffix="$p"
		fi 
	  else
	   fullname=$prefix$p$suffix
	   parts="$parts $fullname"
	  fi
	done

	echo "$pp parts=$parts" >> built/decs.txt
	grep -v "^$pp parts= " "tmp/3$pp" >> built/decs.txt
	
 	if [[ -e "built/$pp" ]] ; then
	 out1="$( stat -f '%m' built/$pp  2> /dev/null)"
	 for k in $parts ; do
	   if [ -e "$k" ] ; then
	    out2="$( stat -f '%m' $k  2> /dev/null)" 
#	    echo "$out1 < $out2" $(( $out1 < $out2))
	    if [ "$(( $out1 < $out2))" == "1" ]  ; then
	     rm -rf "built/$pp"
	     echo "del $pp"
	     break
	    fi
	   else 
	    rm -rf "built/$pp"
	     echo "del $pp"
	    break
	   fi
	 done
	fi
	
	
	for k in $parts ; do 
		if [[ ${k:(-4)} == ".lib" ||  ${k:(-5)} == ".wexe" ]] ; then
		 echo "$k ${k%.*}.libsrc "   >>decs2.txt
		fi

		echo "built/$pp $k "   >>decs2.txt
	done

done

#build outofdate.txt files

rm -fr outofdate.txt 
for f in $(cut -d " " -f1 decs2.txt | sort -u) 
do
 if ! [ -e $f ] ; then
  echo $f >>  outofdate.txt 
 fi
done

if ! [ -e outofdate.txt ] ; then 
 exit 0
fi

cp outofdate.txt new.txt
while(true)
do
ood=$( join   -2 2 -o "2.1"  new.txt <(sort -k 2 decs2.txt ) | sort -u  )

rm -f new.txt
for f in $ood
 do
   if  [ -e $f ] ; then
   rm $f
   echo $f >> new.txt 
   echo $f >> outofdate.txt
  fi 
done

if ! [ -e new.txt ] ; then
break
fi
done

sort outofdate.txt >tmp.txt
mv tmp.txt outofdate.txt

# awk '{ if ($3 < $4)  print $1 ; } ' decs2.txt | sort -u  >  outofdate.txt 

#build processorder.txt

join -1 2 -2 1  -o "1.1 1.2 " <(sort -k 2 decs2.txt) outofdate.txt | sort >tmp/tmp3.txt


echo "" > processorder.txt

set -e

while [ true ]  
do
 join  outofdate.txt tmp/tmp3.txt | sort -u | cut -d " " -f "1" | cat - outofdate.txt | sort | uniq -u > toprocess.txt

 if ! [ -s toprocess.txt  ] ; then
 break
 fi

 cat toprocess.txt >> processorder.txt ; echo "" >>processorder.txt


cat outofdate.txt toprocess.txt |sort | uniq -u > outofdate2.txt 

mv outofdate2.txt outofdate.txt

join  -1 2  -o "1.1 1.2"   <(sort -k 2 tmp/tmp3.txt) outofdate.txt | sort  > tmp/tmp4.txt

 

mv tmp/tmp4.txt tmp/tmp3.txt

done

#cat processorder.txt

for  x in $(cat processorder.txt) 
do
 t=$(basename $x)
 echo "make${t##*.} $t"
 make${t##*.} $t
done

exit