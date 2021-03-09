#!/usr/local/bin/tau   ; use tools; testprofile."stdlib"

; use doc ; doclibrary."stdlib"

 ; use tools; testprofile."stdlib"

testprofile."stdlib"

use tools; testprofile."solardataall"

doclibrary."stdlib"

; use pretty ; pretty("printbitcodes printbitcodes bitcodesupport runcode","junk")

print.compile("baseTypeCheck","stdlib")

; use doc ; doclibrary."stdlib"

; use doc ; doclibrary."stdlib"

; use doc ; doclibrary."tools"

; use main2  ; print.compile("pass2","bug9.core")

; use main2 ;   print.compile("pass2","bug9.core")

; use doc ; doclibrary."stdlib:small"

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

Library tools doc profile genLR1 taulextable
uses stdlib 
exports  doc   profile    tools genLR1 taulextable

* STATE builtin:profile profileinfo profileresult

* only document printbitcodes profile prettylib doc

* usegraph exclude standard seq set

use main2

use profile

use standard

use seq.word

use seq.seq.word
 
Function testprofile(libname:seq.word)seq.word
let a = print.compile("all", libname)
 a + profileresults."time" + dumpprofileinfo