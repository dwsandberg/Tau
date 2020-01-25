#!/usr/local/bin/tau

Module newtools

Library newtools bandeskopf barycenter display displaygraph displaytextgraph doc genLR1 labeledgraph layergraph makeDAG  prettylib printbitcodes profile renamemodule svg svggraph taulextable testparser 
 prettyparagraph
 uses stdlib 
 exports bandeskopf barycenter display displaygraph displaytextgraph doc 
 genLR1 labeledgraph layergraph makeDAG pretty prettylib printbitcodes profile svg svggraph taulextable testparser newtools

/run newtools testfirstpass

run newtools testprofile

/run tools prettytest

run tools callgraphtest

run newtools stdlibdoc

run doc createdoc

/run tools testhtmlcode

/run genLR1 gentau2

/run taulextable getlextable

/run printbitcodes test1

/run tools testprintBitCodes

run tools checkdoclib

* only document printbitcodes profile prettylib doc

* usegraph exclude stdlib seq set

use doc

use main2

use prettylib

use printbitcodes

use profile

use seq.seq.word

use seq.word

Function testhtmlcode seq.word htmlcode."testall"

Function prettytest seq.word prettylib("mytest","")

Function checkdoclib seq.word doclibrary."tools"

Function testfirstpass seq.word 
 @(+, +."&br &br","", firstPass("testall"_1))

Function testprofile seq.word 
 let a = compilelib2("stdlib"_1)
  a + profileresults."time"

Function testprintBitCodes seq.word printBitCodes."test4.bc"

Function callgraphtest seq.word 
 callgraphbetween("stdlib","libdescfunc other main2")

Function stdlibdoc seq.word 
 // callgraphwithin("stdlib","llvm")+ // doclibrary."stdlib"

