#!/usr/local/bin/tau

Library tools bandeskopf barycenter displaygraph displaytextgraph doc labeledgraph layergraph makeDAG prettylib printbitcodes profile svg svggraph 
 uses stdlib 
 exports bandeskopf barycenter displaygraph displaytextgraph doc layergraph makeDAG prettylib prettylib printbitcodes profile svg svggraph tools

Module tools

/run tools prettytest

/run printbitcodes test2

run tools test2

run tools stdlibdoc

/run doc createdoc

/run tools testprintBitCodes

run tools test

run tools checkdoclib

run tools test1

run doc createdoc

* usegraph exclude stdlib seq set

use doc

use main

use prettylib

use printbitcodes

use profile

use seq.word

Function test1 seq.word htmlcode."tools"

Function checkbind seq.word checkbind."tools"

Function prettytest seq.word prettylib."tools"

Function checkdoclib seq.word doclibrary."tools"

Function test seq.word 
 let a = compilelib("solardataall"_1)
  a + profileresults."time"

Function testprintBitCodes seq.word printBitCodes."test2.bc"

Function stdlibdoc seq.word 
 callgraphbetween("stdlib","llvm internalbc")+ // callgraphwithin("stdlib","llvm")+ // doclibrary."stdlib"

Function test2 seq.word doclibrary."basic"

