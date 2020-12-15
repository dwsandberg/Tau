#!/usr/local/bin/tau    ; use doc ; callgraphwithin("stdlib:testoptconfig","testopt")

; use tools; testprofile."solardataall"

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

Library tools  
doc    profile     
uses stdlib
exports bandeskopf barycenter display displaygraph displaytextgraph doc 
labeledgraph layergraph makeDAG pretty profile  svggraph  tools

* STATE builtin:profile profileinfo profileresult

* only document printbitcodes profile prettylib doc

* usegraph exclude standard seq set

use main2

use profile

use standard

use seq.seq.word

use seq.word

 
Function testprofile(libname:seq.word)seq.word
 let a = print.compile("all", libname)
  a + profileresults."time"

+ dumpprofileinfo
