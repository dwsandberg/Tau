build=built
set -e

libtype="bc" 

myhost="https://myhost.local/"

export tauopen=open 

#export tauDylib="tauexe "

function linklibrary { 	 
 if [ -z "$norun" ];then
   if [ -z $tauDylib ];then         
       echo '#define  BT long long int' > $build/$1.c 
		echo "BT entrypoint$1(BT,BT); BT mainentry(BT a,BT b){return entrypoint$1(a,b);}" >> $build/$1.c 
		dependlibs="dependlibs_$1"    
		cmd="clang -lm -pthread tau2bc/*.c $build/$1.c ${!dependlibs} $build/$1.bc -o $build/$1.lib  "
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
 tmpvar=taubc 
 dependlibs=
 cp bin/${tmpvar}.bc $build
 linklibrary ${tmpvar}
 mv $build/${tmpvar}.lib $build/taubc0.lib
 cc bin/putfile.c -o bin/putfile.cgi
 #now get the default llvm layout for machine
 cc -S -emit-llvm bin/putfile.c 
 awk '/^target d/{print "\nFunction",$2, "seq.word",$4}\
 /^target t/{print "\nFunction",$2, "seq.word",$4,""}
 ' putfile.ll \
 | cat bin/tauconfig.ls -  >tau2bc/tauconfig.ls
 #rm putfile.ll
 echo " " > $build/start.ls
 echo "finish start"
} 

if ! [ -e $build ] ; then 
mkdir -m 776 $build # mode is specified so local web server in same group as user can access it
startfresh
fi

 
for x in $@ 
do
 if [ -z $partname ] ; then
     partname=$(basename $x .bld)
 else 
 partname=${partname}_$(basename $x .bld)
 fi 
done

scriptname=$build/build_$partname 
oldscript=${scriptname}old.sh
sharoot=$build/sharoot.txt
tarname=~/taubackups/${partname}/$(date +%Y%m%d%H%M)

rm -f  $sharoot; touch  $sharoot # make sure file exists but is empty

if [[ -f $oldscript ]] ;then
 #hash any files that may be needed for  this built
 makehash=true #change the behavior of script to just return changelist and unchangedlist.
 source $oldscript
 makehash= #change behavior 
 for x in $changelist $unchangelist 
  do
   if [[  -f $x ]] ;then
   shasum $x >> $sharoot
   fi
  done
else
 touch $oldscript #must have oldscript file for parameter to makeScript
fi 

rm -f error.html

#now built script to do actual changes.
$build/taubc0.lib makeScript   $@ builddir:+$build hashes: $sharoot $oldscript   o:$scriptname.sh 

if [ -e error.html ] ; then
$tauopen error.html
exit 1
fi

#run the script that was just created. 
 
source $scriptname.sh

#upon success completion of script save copy of script.
#this allows detection of any files whose contents have changed since last update  
#by compare shasum hashes of the saved copy of the script with the current hashs

mv  ${scriptname}.sh $oldscript 
mkdir -p $(dirname   $tarname)
tar -zcf $tarname.tar.gz --exclude="$build/*" $unchangelist  $changelist 
echo "tarname= $tarname"
echo "finish tar"
