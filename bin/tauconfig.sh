#export tauDylib="tauexe "
export tauopen=open 


if ! [ -e built ] ; then 
mkdir tmp
mkdir built
echo "" > B
echo "" >> B
echo "void init_stdlib(); void init_libs(){init_stdlib(); }">built/stdlib.c
clang -lm -pthread  stdlib/*.c built/stdlib.c bin/stdlib.bc  -o built/stdlib
cc bin/putfile.c -o bin/putfile.cgi
fi

libtype="bc" 
function outofdate { 
stat -f '%N %m' $parts > tmp.txt 2> /dev/null || return 1 
X=$(sort -k2 tmp.txt | tail -n 1) 
lastupdated=${X%%\ *} 
first=${parts%%\ *} 
[[ $lastupdated == $first ]]&& return 0 
return 2 
} 

function libexe {
 rm -f built/error.html
 allargs="$@"
 restargs="${allargs#*\ }"
built/${tauDylib}$1 $restargs
 if  [ -e built/error.html ] ; then
  $tauopen built/error.html  
  exit 1
 fi

}

function runlib { 
if [ -z"$tauDylib" ];then 
echo "void init_$1(); $ccode init_$1();}"> built/$1.c 
cmd="clang -lm -pthread stdlib/*.c built/$1.c $dependlibs built/$1.bc -o built/$1 "
echo $cmd
$cmd
else 
libtype="dylib" 
clang -lm -pthread -dynamiclib built/$1.bc $dependlibs -o built/$1.dylib -init_init_$1 -undefined dynamic_lookup 
fi 
echo "done"> built/$1.lib  
} 

export -f runlib
export -f outofdate
export -f libexe 