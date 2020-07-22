#!/usr/local/bin/tau

Module tools

cd stdlib
ln bits.ls blockseq.ls deepcopy.ls graph.ls ipair.ls oseq.ls process.ls  seq.ls set.ls
tree.ls xxhash.ls ~/work/jstest

different than stdlib.s packedseq.ls real.ls stdlib.ls UTF8.ls 

Library tools bandeskopf barycenter display displaygraph displaytextgraph doc genLR1 labeledgraph layergraph makeDAG 
 printbitcodes profile  svg svggraph taulextable testparser 
 uses stdlib 
 exports bandeskopf barycenter display displaygraph displaytextgraph doc genLR1 labeledgraph layergraph 
 makeDAG pretty  printbitcodes profile svg svggraph taulextable testparser tools
 
* STATE   builtin:profile profileinfo   profileresult  


/run printbitcodes test1

/run tools testfirstpass

/run tools testprofile

/run tools prettytest

/run tools callgraphtest

run tools stdlibdoc

run doc createdoc

/run tools testhtmlcode

/run genLR1 gentau2

/run taulextable getlextable


/run tools testprintBitCodes

run tools checkdoclib

* only document printbitcodes profile prettylib doc

* usegraph exclude stdlib seq set

use doc

use main2

use newpretty 

use printbitcodes

use profile

use seq.seq.word

use seq.word

use stdlib

Function testhtmlcode seq.word htmlcode."testall"

/Function prettytest seq.word prettylib("test4","")

Function checkdoclib seq.word doclibrary."mylib"

Function testfirstpass seq.word @(+, +("&br &br "),"", firstPass("testall"_1))

Function testprofile seq.word 
   let a = compilelib2("mylib"_1)
    a + profileresults."time"
    
    +dumpprofileinfo

Function testprintBitCodes seq.word printBitCodes."test4.bc"

Function callgraphtest seq.word callgraphbetween("testall","test5  testall test2 stdlib")
+callgraphwithin("stdlib","llvm")

Function stdlibdoc seq.word   // callgraphbetween("stdlib","codegennew persistant")+ //    doclibrary."stdlib"


