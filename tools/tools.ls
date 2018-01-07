#!/usr/local/bin/tau

Library tools bandeskopf barycenter displaygraph displaytextgraph layergraph makeDAG prettylib svg svggraph doc
profile labeledgraph printbitcodes
 uses stdlib 
 exports prettylib tools doc profile printbitcodes prettylib
 

Module tools

run tools stdlibdoc

/run doc createdoc

/run tools testprintBitCodes

run tools test

run tools checkdoclib

run tools test1

run doc createdoc

* usegraph exclude stdlib seq set

use doc

use prettylib

use profile

use main

use seq.word

use printbitcodes

Function test1 seq.word htmlcode."tools"

Function checkbind seq.word checkbind."tools"

Function prettytest seq.word prettylib."tools"

Function checkdoclib seq.word doclibrary."tools"

Function test seq.word 
 let a = compilelib("solardataall"_1)
  a + profileresults."time"

Function testprintBitCodes seq.word printBitCodes."test3.bc"

Function stdlibdoc seq.word       callgraphbetween("stdlib","llvm internalbc")   +
// callgraphwithin("stdlib","llvm")
+ //
doclibrary("stdlib")

