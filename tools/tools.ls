#!/usr/local/bin/tau

Library tools bandeskopf barycenter displaygraph displaytextgraph doc labeledgraph layergraph makeDAG 
prettylib printbitcodes profile renamemodule svg svggraph 
 uses stdlib 
 exports bandeskopf barycenter displaygraph displaytextgraph doc layergraph makeDAG prettylib prettylib printbitcodes profile svg svggraph tools

Module tools

/run tools test

/run tools prettytest

/run printbitcodes test1

/run tools test2

/run tools stdlibdoc

/run doc createdoc

/run tools testprintBitCodes

/run tools test

run tools checkdoclib

run tools test1

run doc createdoc

* only document  printbitcodes profile prettylib doc

* usegraph exclude stdlib seq set

use doc

use main

use prettylib

use printbitcodes

use profile

use seq.word

Function test1 seq.word htmlcode."tools"

Function checkbind seq.word checkbind."tools"

Function prettytest seq.word prettylib("test1","")

"byteseq bitpackedseq codegen2 codegen codetemplates2 codetemplates definestruct2 definestruct fileresult textio persistant2 persistant pretty2 pretty")

Function checkdoclib seq.word   doclibrary."stdlib"

callgraphbetween("newimp","libdescfunc libscope doc")  

doclibrary."tools"

use seq.word

Function test seq.word 
 let a = compilelib("stdlib"_1)
  a + profileresults."time"

Function testprintBitCodes seq.word printBitCodes."mytest.bc"

Function stdlibdoc seq.word 
 // callgraphwithin("stdlib","llvm")+ // doclibrary."stdlib"

Function test2 seq.word 
 callgraphbetween("useful","useful processtypes")+ doclibrary."tools"

