#!/usr/local/bin/tau

Module tools

cd stdlib
ln bits.ls blockseq.ls deepcopy.ls graph.ls ipair.ls oseq.ls process.ls  seq.ls set.ls
tree.ls xxhash.ls ~/work/jstest

different than stdlib.s packedseq.ls real.ls stdlib.ls UTF8.ls 

Library tools bandeskopf barycenter display displaygraph displaytextgraph doc genLR1 labeledgraph layergraph makeDAG prettylib prettyparagraph printbitcodes profile renamemodule svg svggraph taulextable testparser 
 uses stdlib 
 exports bandeskopf barycenter display displaygraph displaytextgraph doc genLR1 labeledgraph layergraph 
 makeDAG pretty prettylib printbitcodes profile svg svggraph taulextable testparser tools

/run printbitcodes test1

/run tools testfirstpass

run tools testprofile

/run tools prettytest

/run tools callgraphtest

run tools stdlibdoc

/run doc createdoc

run tools testhtmlcode

run genLR1 gentau2

run taulextable getlextable


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

use stdlib

Function testhtmlcode seq.word htmlcode."testall"

Function prettytest seq.word prettylib("test4","")

Function checkdoclib seq.word doclibrary."tools"

Function testfirstpass seq.word @(+, +("&br &br "),"", firstPass("testall"_1))

Function testprofile seq.word 
   let a = compilelib2("stdlib"_1)
    a + profileresults."time"

Function testprintBitCodes seq.word printBitCodes."test4.bc"

Function callgraphtest seq.word callgraphbetween("stdlib","libdescfunc other main2")

Function stdlibdoc seq.word // callgraphwithin("stdlib","llvm")+ // doclibrary."stdlib"

