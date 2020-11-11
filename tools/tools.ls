#!/usr/local/bin/tau

Module tools


Library tools bandeskopf barycenter display displaygraph displaytextgraph doc genLR1 labeledgraph layergraph makeDAG 
  profile  svg svggraph taulextable testparser 
 uses stdlib 
 exports bandeskopf barycenter display displaygraph displaytextgraph doc genLR1 labeledgraph layergraph 
 makeDAG pretty   profile svg svggraph taulextable testparser tools
 
* STATE   builtin:profile profileinfo   profileresult  


/run tools testsecondpass
 
/run tools testfirstpass

run tools testprofile

/run tools prettytest

/run tools callgraphtest

run tools stdlibdoc

/run doc createdoc

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

use profile

use seq.seq.word

use seq.word

use stdlib

Function testhtmlcode seq.word htmlcode."testall"

/Function prettytest seq.word prettylib("test4","")

Function checkdoclib seq.word doclibrary."mylib"

Function testfirstpass seq.word @(+, +("&br &br "),"", firstPass("testall"_1))

Function testsecondpass seq.word @(+, +("&br &br "),"", secondPass("simpletest"_1))


Function testprofile seq.word 
   let a = compilelib2("mylib"_1)
    a + profileresults."time"
    
    +dumpprofileinfo

 
Function callgraphtest seq.word callgraphbetween("testall","test5  testall test2 stdlib")
+callgraphwithin("stdlib","llvm")

Function stdlibdoc seq.word    //   callgraphbetween("stdlib","codegennew persistant")+  //     doclibrary."stdlib"


