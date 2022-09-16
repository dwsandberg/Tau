build=built
set -e

function checksrc {
     mkdir -p "$build/src/$(dirname $1)"
    ln  -f $1 "$build/src/$1" 
}

#export tauDylib="tauexe "

export tauopen=open 


libtype="bc" 


function libexe {
 rm -f error.html
 allargs="$@"
 [[ "${allargs#*o=}" != $allargs ]] && rm  -f built/${allargs#*o=}
 #echo "running ${allargs::40}"
 if [ -z "$norun" ];then
 echo building $node
 restargs="${allargs#*\ }"
$build/${tauDylib}$1.lib $restargs > /dev/null
 else
   echo "make built/${allargs#*o=}"
fi
 if  [ -e  error.html ] ; then
  $tauopen  error.html  
  mv sums.txt built/oldsums.txt
  exit 1
 fi
}

function libexeAll {
h1=$(cat $dependsOn 2> /dev/null | shasum)
if [[ -e $node ]] ;then
      hashline="$node ${h1::40}"
else 
     hashline="?"
fi 
if    grep "${hashline}" built/oldsums.txt > /dev/null ; then
  echo $hashline >> sums.txt
  else 
  libexe $@ 
  if [ -z "$norun" ];then
    echo "$node ${h1::40}" >> sums.txt
  fi
fi
}


function makelibrary {
   h1=$(cat $dependsOn 2> /dev/null | shasum)
#   if [[ -e $build/$1.lib ]] ; then 
   hashline="$1 ${h1::40}"
#   else
#    hashline="?"
#   fi
 if   grep "${hashline}" built/oldsums.txt > /dev/null ; then
  echo $hashline >> sums.txt
  else 
      node=$1.libsrc
      libexe $libsrcargs
      node=$1.$libtype
     libexe $compileargs
 if [ -z "$norun" ];then
 	 if [ -z $tauDylib ];then 
		echo "void init_$1(); $ccode init_$1();}"> $build/$1.c 
		cmd="clang -lm -pthread stdlib/*.c $build/$1.c $dependlibs $build/$1.bc -o $build/$1.lib  "
		echo $cmd
		$cmd
	 else 
	   cmd=" clang -dynamiclib $build/$1.bc  -o $build/$1.lib  -init _init_$1 -undefined dynamic_lookup"
	   echo $cmd
	   $cmd
    fi 
	 echo $hashline >> sums.txt
else 
  echo makelibrary "$build/$1.lib"
fi
  fi
}

if ! [ -e $build ] ; then 
mkdir $build
echo "" >> $build/oldsums.txt
echo "void init_stdlib(); void init_libs(){init_stdlib(); }">$build/orgstdlib.c
clang -lm -pthread  stdlib/*.c $build/orgstdlib.c bin/stdlib.bc  -o $build/orgstdlib.lib
cc bin/putfile.c -o bin/putfile.cgi
#clang -dynamiclib bin/stdlib.bc  -o $build/orgstdlib.lib  -init _init_stdlib -undefined dynamic_lookup
#cc  stdlib/*.c -DLIBRARY -o built/tauexe

fi


checksrc bin/stdlib.bc
checksrc bin/taubuild.sh
checksrc stdlib/tau.c
checksrc stdlib/tauthreads.c
checksrc stdlib/tau.h
checksrc bin/putfile.c

echo "$0 $@" > $build/src/bin/buildcommand.sh

export -f libexe 


if [[ $1 == "-n" ]]; then
tmpnorun=true
shift 1
fi
 cd $build/src
rm -f $@  
cd ..
cd ..
cp $@ $build/src
 
libexe orgstdlib updatestate   $@  o=+$build update.sh 
norun=$tmpnorun
export norun
source  $build/update.sh

if  [ -z "$norun" ];then
mv sums.txt $build/oldsums.txt
cd $build
tar -zcf ~/backup2/$(date +%Y%m%d%H%M).tar.gz src
echo "finish tar"
fi 