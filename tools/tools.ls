#!/usr/local/bin/tau  ; use tools ; test3


;  use doc ; doclibrary."webassembly"

 use doc ; callgraphwithin("webassembly","wasm2")



use doc ; doclibrary."tools"


; use doc ; doclibrary."stdlib"

; use doc ; callgraphbetween("stdlib","mytype passsymbol")

doclibrary."stdlib"

; use tools; testprofile."stdlib"

; use doc ; doclibrary."stdlib"

; use doc ; callgraphbetween("stdlib","UTF8 codegennew otherseq")

; use doc ; doclibrary."typepass"

; use doc ; callgraphbetween("typepass","passparse passsymbol")

; use tools; testprofile."stdlib"

; use doc ; callgraphwithin("typepass","typepass")

; use doc ; doclibrary("typepass")

; use doc ; doclibrary."stdlib"

; use doc ; callgraphwithin("webassembly","wasm2")

; use doc ; doclibrary."webassembly"

; use doc ; callgraphwithin("stdlib","outstream")

; use tools; testprofile."solardataall"

; use pretty ; pretty("printbitcodes printbitcodes bitcodesupport runcode","junk")

print.compile("baseTypeCheck","stdlib")

; use main2 ; print.compile("pass2","bug9.core")

; use doc ; doclibrary."stdlib:small"

; use doc ; doclibrary."tools"

; use taulextable ; getlextable

; use doc ; callgraphbetween("stdlib","UTF8 codegennew otherseq")

; use doc ; callgraphwithin("stdlib","llvm")

; use doc ; htmlcode."testall"

; use genLR1 ; gentau2

Module tools

Library tools baseTypeCheck bandeskopf svg2graph doc genLR1 profile  taulextable
prettycompilerfront
uses stdlib
exports baseTypeCheck doc genLR1 profile taulextable tools  uniqueids wordgraph



* STATE builtin:profile profileinfo profileresult

* only document printbitcodes profile prettylib doc 

* usegraph exclude standard seq set

use main2

use profile

use standard

use seq.word

use seq.seq.word

use prettycompilerfront

Function testprofile(libname:seq.word)seq.word subcompilelib.libname + profileresults."time"

Function test3 seq.word 
totext(compilerfront("text","stdlib"),"junk"
,[rename("seq.T:findelement(T,seq.T) seq.T","lookup",[2,1])
,rename("set.symdef:findelement(symdef,set.symdef) set.symdef","lookup",[2,1])
,rename("set.passtypes:findelement(passtypes,set.passtypes) set.passtypes","lookup",[2,1])
,rename("set.passsymbols:findelement(passsymbols,set.passsymbols) set.passsymbols","lookup",[2,1])
,rename("set.typeentry:findelement(typeentry,set.typeentry) set.typeentry","lookup",[2,1])
]
)





