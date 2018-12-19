#!/usr/local/bin/tau

prettylib  pretty doc profile

Library tools bandeskopf barycenter displaygraph displaytextgraph  labeledgraph layergraph makeDAG 
 printbitcodes  svg svggraph   profile pretty doc prettylib
display
 uses stdlib 
 exports bandeskopf barycenter displaygraph displaytextgraph doc layergraph makeDAG   prettylib printbitcodes profile svg 
 svggraph tools labeledgraph display pretty

Module tools


run tools test

/run tools prettytest

/run printbitcodes test1

/run tools test2

/run newtools stdlibdoc

/run doc createdoc

/run tools testprintBitCodes

/run tools test

run newtools checkdoclib


run doc createdoc

* only document  printbitcodes profile prettylib doc

* usegraph exclude stdlib seq set

use doc

use main2

/use prettylib

use printbitcodes

use profile

use seq.word

/Function test1 seq.word htmlcode."test11"


/Function prettytest seq.word prettylib("test4","")

"byteseq bitpackedseq codegen2 codegen codetemplates2 codetemplates definestruct2 definestruct fileresult textio persistant2 persistant pretty2 pretty")

Function checkdoclib seq.word   doclibrary."newtools"

callgraphbetween("newimp","libdescfunc libscope doc")  

doclibrary."tools"

use seq.word

Function test seq.word 
 let a = compilelib2("stdlib"_1)
  a + profileresults."time"

Function testprintBitCodes seq.word printBitCodes."mytest.bc"

/Function stdlibdoc seq.word 
 // callgraphwithin("stdlib","llvm")+ // doclibrary."stdlib"

/Function test2 seq.word 
 callgraphbetween("useful","useful processtypes")+ doclibrary."tools"

