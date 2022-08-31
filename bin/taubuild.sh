#rm -r built
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
 rm -f $build/error.html
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
 if  [ -e $build/error.html ] ; then
  $tauopen $build/error.html  
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
   hashline="$1 ${h1::40}"
 if   grep "${hashline}" built/oldsums.txt > /dev/null ; then
  echo $hashline >> sums.txt
  else 
      libexe $libsrcargs
     libexe $compileargs
 if [ -z "$norun" ];then
 	 if [ -z"$tauDylib" ];then 
		echo "void init_$1(); $ccode init_$1();}"> $build/$1.c 
		cmd="clang -lm -pthread stdlib/*.c $build/$1.c $dependlibs $build/$1.bc -o $build/$1.lib  "
		echo $cmd
		$cmd
	 else 
		libtype="dylib" 
		clang -lm -pthread -dynamiclib $build/$1.bc $dependlibs -o $build/$1.dylib -init_init_$1 -undefined dynamic_lookup 
	 fi 
	 echo $hashline >> sums.txt
else 
  echo makelibrary "$build/$1.lib"
fi
  fi
}


function  mkbuild {
if  [ -z "$norun" ];then
mv sums.txt built/oldsums.txt
cd $build
tar -zcf ~/backup2/save$(date +%Y%m%d%H%M.bak).tar.gz src
echo "finish tar"
fi 
}


if ! [ -e $build ] ; then 
mkdir $build
echo "" >> $build/oldsums.txt
echo "void init_stdlib(); void init_libs(){init_stdlib(); }">$build/stdlib.c
clang -lm -pthread  stdlib/*.c $build/stdlib.c bin/stdlib.bc  -o $build/stdlib.lib
ln $build/stdlib.lib $build/orgstdlib.lib
cc bin/putfile.c -o bin/putfile.cgi
fi




checksrc bin/stdlib.libinfo
checksrc bin/stdlib.bc
checksrc bin/taubuild.sh
checksrc stdlib/tau.c
checksrc stdlib/tauthreads.c
checksrc stdlib/tau.h
checksrc bin/putfile.c
checksrc bin/all.decs

echo "$0 $@" > $build/src/bin/buildcommand.sh

export -f libexe 


if [[ $1 == "-n" ]]; then
tmpnorun=true
shift 1
fi
if ! [ -z "$@" ];then
cp $@ built/src
fi
libexe stdlib updatestate  bin/all.decs  $@  o=update.sh 
norun=$tmpnorun
export norun
source  built/update.sh

if  [ -z "$norun" ];then
mv sums.txt built/oldsums.txt
cd $build
tar -zcf ~/backup2/save$(date +%Y%m%d%H%M.bak).tar.gz src
echo "finish tar"
fi 