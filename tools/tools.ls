#!/usr/local/bin/tau

prettylib  pretty doc profile

Library tools bandeskopf barycenter displaygraph displaytextgraph  labeledgraph layergraph makeDAG 
 printbitcodes  svg svggraph   profile pretty doc prettylib renamemodule
 genLR1 testparser taulextable
display
 uses stdlib 
 exports bandeskopf barycenter displaygraph displaytextgraph doc layergraph makeDAG   prettylib printbitcodes profile svg 
 svggraph tools labeledgraph display pretty genLR1 testparser taulextable

Module tools

/run tools testfirstpass

/run tools testprofile

/run tools prettytest

run tools stdlibdoc

run doc createdoc

/run tools testhtmlcode 

/run genLR1 gentau2

/run taulextable getlextable



/run printbitcodes test1


run tools testprintBitCodes

run tools checkdoclib

* only document  printbitcodes profile prettylib doc

* usegraph exclude stdlib seq set

use doc

use main2

use prettylib

use printbitcodes

use profile

use seq.word

Function testhtmlcode seq.word htmlcode."testall"


Function prettytest seq.word prettylib("stdlib2","")


Function checkdoclib seq.word    doclibrary."tools"

callgraphbetween("stdlib","libdescfunc libscope")  

doclibrary."tools"


Function testfirstpass seq.word 
@(+,   +("&br &br"),"", firstPass("testall"_1))

use seq.seq.word

Function testprofile seq.word 
 let a = compilelib2("stdlib"_1)
  a + profileresults."time"

Function testprintBitCodes seq.word printBitCodes."test4.bc"

Function stdlibdoc seq.word 
 // callgraphwithin("stdlib","llvm")+ // doclibrary."stdlib"


