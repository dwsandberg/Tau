build=built
set -e

libtype="bc" 

export tauopen=open 

#export tauDylib="tauexe "
 
function checksrc {
 for fn in $@ 
 do
     mkdir -p "$build/src/$(dirname $fn)"
    ln  -f $fn "$build/src/$fn" 
 done 
}



function linklibrary { 	 
 if [ -z "$norun" ];then
   if [ -z $tauDylib ];then         
       echo '#define  BT long long int' > $build/$1.c 
		echo "BT entrypoint$1(BT,BT); BT mainentry(BT a,BT b){return entrypoint$1(a,b);}" >> $build/$1.c 
		dependlibs="dependlibs_$1"    
		cmd="clang -lm -pthread stdlib/*.c $build/$1.c ${!dependlibs} $build/$1.bc -o $build/$1.lib  "
		echo $cmd
		$cmd
	 else 
	   cmd=" clang -dynamiclib $build/$1.bc  -o $build/$1.lib  -init _init_$1 -undefined dynamic_lookup"
	   echo $cmd
	   $cmd
    fi 
fi
}

function startfresh {
 dependlibs=
 cp bin/stdlib.bc $build
 linklibrary stdlib
mv $build/stdlib.lib $build/orgstdlib.lib
cc bin/putfile.c -o bin/putfile.cgi
echo " " > $build/start.ls
} 

if ! [ -e $build ] ; then 
mkdir $build
 startfresh 
 checksrc bin/stdlib.bc
 checksrc bin/taubuild.sh
 checksrc stdlib/tau.c
 checksrc stdlib/tauthreads.c
 checksrc stdlib/tau.h
 checksrc bin/putfile.c
fi

h11=$(echo $@ | shasum )

scriptname=$build/build

for x in $@ 
do
 scriptname=${scriptname}_$(basename $x .bld) 
done

scriptname=${scriptname}_${h11::10}.sh


sharoot=$build/sharoot.txt

oldscript=${scriptname}old

rm -f  $sharoot; touch  $sharoot ; touch $oldscript
if [[ -f $oldscript ]] ;then
makehash=true
source $oldscript
rm -f  $sharoot; touch  $sharoot ;  
for x in $changelist $unchangelist 
do
 if [[  -f $x ]] ;then
 shasum $x >> $sharoot
 fi
done
makehash=
fi

if [[   $1 == "-n" ]]; then
tmpnorun=true
shift 1
fi


checksrc $1

rm -f error.html



$build/orgstdlib.lib makeScript2  $@ builddir=+$build hashes= $sharoot $oldscript   o=$scriptname 



if [ -e error.html ] ; then
$tauopen error.html
exit 1
fi

norun=$tmpnorun



source $scriptname

if  [ -z "$norun" ];then
mv  $scriptname $oldscript  
cd $build
tar -zcf  ~/backup2/$(date +%Y%m%d%H%M).tar.gz --exclude='./$build/*' src
echo "finish tar"
fi 