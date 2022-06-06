#export tauDylib="tauexe "
export tauopen=open 
build=built

if ! [ -e $build ] ; then 
mkdir $build
echo "void init_stdlib(); void init_libs(){init_stdlib(); }">$build/stdlib.c
clang -lm -pthread  stdlib/*.c $build/stdlib.c bin/stdlib.bc  -o $build/stdlib.lib
ln $build/stdlib.lib $build/orgstdlib.lib
cc bin/putfile.c -o bin/putfile.cgi
fi

libtype="bc" 
function outofdate { 
stat -f '%N %m' $parts > tmp.txt 2> /dev/null || return 1 
X=$(sort -rsk2 tmp.txt | head -n 1) 
lastupdated=${X%%\ *} 
first=${parts%%\ *} 
[[ $lastupdated == $first ]]&& return 0 
if [ -z "$norun" ];then
  return 2
else 
  echo "$parts"
  return 0
fi
} 

function libexe {
 rm -f $build/error.html
 allargs="$@"
 [[ "${allargs#*o=}" != $allargs ]] && rm  -f built/${allargs#*o=}
 echo "running ${allargs::40}"
 restargs="${allargs#*\ }"
$build/${tauDylib}$1.lib $restargs > /dev/null
 if  [ -e $build/error.html ] ; then
  $tauopen $build/error.html  
  exit 1
 fi

}

function runlib { 
if [ -z"$tauDylib" ];then 
echo "void init_$1(); $ccode init_$1();}"> $build/$1.c 
cmd="clang -lm -pthread stdlib/*.c $build/$1.c $dependlibs $build/$1.bc -o $build/$1.lib  "
echo $cmd
$cmd
else 
libtype="dylib" 
clang -lm -pthread -dynamiclib $build/$1.bc $dependlibs -o $build/$1.dylib -init_init_$1 -undefined dynamic_lookup 
fi 
} 

function checksrc {
     mkdir -p "$build/src/$(dirname $1)"
    ln  -f $1 "$build/src/$1" 
}

function  mkbuild {
if  [ -z "$norun" ];then
cd $build
tar -zcf ~/backup2/save$(date +%Y%m%d%H%M.bak).tar.gz src
echo "finish tar"
fi 
}

checksrc bin/stdlib.libinfo
checksrc bin/stdlib.bc
checksrc bin/tauconfig.sh
checksrc stdlib/tau.c
checksrc stdlib/tauthreads.c
checksrc stdlib/tau.h
checksrc bin/putfile.c
checksrc simple/all.decs

cp $0 $build/src/bin/build.sh


export -f runlib
export -f outofdate
export -f libexe 