build=built
set -e

libtype="bc" 

export tauopen=open 

#export tauDylib="tauexe "
 
function checksrc {
     mkdir -p "$build/src/$(dirname $1)"
    ln  -f $1 "$build/src/$1" 
}

function libexe {
 rm -f error.html
 allargs="$@"
 if [ -z "$norun" ];then
 echo "building ${allargs#*o=}"
 restargs="${allargs#*\ }"
 echo "$build/${tauDylib}$1.lib $restargs > /dev/null"
$build/${tauDylib}$1.lib $restargs > /dev/null
 else
   echo "make built/${allargs#*o=}"
fi
 if  [ -e  error.html ] ; then
  $tauopen  error.html  
#  mv sums.txt built/oldsums.txt
  exit 1
 fi
}

function linklibrary { 	 
 if [ -z "$norun" ];then
   if [ -z $tauDylib ];then         
       echo '#define  BT long long int' > $build/$1.c 
		echo "BT entrypoint$1(BT,BT); BT mainentry(BT a,BT b){return entrypoint$1(a,b);}" >> $build/$1.c 
		cmd="clang -lm -pthread stdlib/*.c $build/$1.c $dependlibs $build/$1.bc -o $build/$1.lib  "
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
sharoot=${h11::10}.txt


cd ./built/src
list=$(find  . -type f -print)
cd ../..
rm -f $build/$sharoot; touch $build/$sharoot
for x in $list
do
 if [[  -f $x ]] ;then
 shasum $x >> $build/$sharoot
 fi
done

if [[ ! -f $build/old$sharoot ]] ; then
    echo "X" >  $build/old$sharoot 
 fi

if [[   $1 == "-n" ]]; then
tmpnorun=true
shift 1
fi


checksrc $1

libexe orgstdlib updatestate2 +$build old$sharoot  $sharoot +.bld $@ builddir=+built o=+$build update2.sh 

norun=$tmpnorun

source built/update2.sh

if  [ -z "$norun" ];then
mv  $build/old$sharoot $build/oldold$sharoot
mv  $build/$sharoot $build/old$sharoot
cd $build
tar -zcf  ~/backup2/$(date +%Y%m%d%H%M).tar.gz --exclude='./built/*' src
echo "finish tar"
fi 