#!/usr/local/bin/tau ;  use doc ; callgraphbetween("stdlib","codetemplates encoding graph intdict libdesc otherseq  ")

; use tools; testprofile."stdlibbak"

; use doc ; doclibrary."tools"

; use taulextable ; getlextable

; use doc ; doclibrary."stdlib"

; use doc ; callgraphbetween("stdlib","UTF8 codegennew otherseq  ")

; use doc ; callgraphwithin("stdlib","llvm")

; use pretty ; htmlcode."testall"

; use main2 ; use tools ; asparagraphs.compile("pass1","testall")

; use main2 ; use tools ; asparagraphs.compile("pass2","testall")

; use genLR1 ; gentau2

Module tools

Library tools bandeskopf barycenter display displaygraph displaytextgraph doc genLR1 labeledgraph layergraph makeDAG profile svg svggraph taulextable testparser
uses stdlib
exports bandeskopf barycenter display displaygraph displaytextgraph doc genLR1 labeledgraph layergraph makeDAG pretty profile svg svggraph taulextable testparser tools

* STATE builtin:profile profileinfo profileresult

* only document printbitcodes profile prettylib doc

* usegraph exclude stdlib seq set

use main2

use profile

use stdlib

use seq.seq.word

use seq.word

Function asparagraphs(a:seq.seq.word)seq.word a @ +(""," &br  &br" + @e)

Function testprofile(libname:seq.word)seq.word
 let a = asparagraphs.compile("all", libname)
  a + profileresults."time"

+ dumpprofileinfo
