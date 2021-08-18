#!/usr/local/bin/tau ;  use doc ; doclibrary."stdlib"

 ; use doc ; callgraphbetween("stdlib","UTF8 codegennew otherseq  ")

; use doc ; doclibrary."typepass"

; use doc ; callgraphbetween("typepass","passparse passsymbol   ")

; use tools; testprofile."stdlib"

; use doc ; callgraphwithin("typepass","typepass")

; use doc ; doclibrary("typepass" )

; use doc ; doclibrary."stdlib"

; use doc ; callgraphwithin("webassembly","wasm2")

; use doc ; doclibrary."webassembly"

; use doc ; callgraphwithin("stdlib","outstream")

; use tools; testprofile."solardataall"

; use pretty ; pretty("printbitcodes printbitcodes bitcodesupport runcode","junk")

print.compile("baseTypeCheck","stdlib")

; use main2  ; print.compile("pass2","bug9.core")

; use doc ; doclibrary."stdlib:small"

; use doc ; doclibrary."tools"

; use taulextable ; getlextable

; use doc ; callgraphbetween("stdlib","UTF8 codegennew otherseq  ")

; use doc ; callgraphwithin("stdlib","llvm")

; use pretty ; htmlcode."testall"

; use genLR1 ; gentau2

Module tools

Library tools  genLR1 profile taulextable   doc baseTypeCheck
uses stdlib 
exports doc genLR1 profile taulextable tools baseTypeCheck

 

* STATE builtin:profile profileinfo profileresult

* only document printbitcodes profile prettylib doc

* usegraph exclude standard seq set

use main2

use profile

use standard

use seq.word

use seq.seq.word
 
Function testprofile(libname:seq.word)seq.word
 subcompilelib(libname)+ profileresults."time" + dumpprofileinfo