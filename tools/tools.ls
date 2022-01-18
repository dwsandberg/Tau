#!/bin/sh  tau stdlib tools pretty wtest1 tausupport bits bitstream format set textio stack encoding otherseq process real seq standard UTF8 words xxhash

tau stdlib tools test3  wtest1

pretty wtest1 .

test3

pretty  webassembly inputoutput



Module tools

Library tools baseTypeCheck bandeskopf svg2graph doc genLR1 profile  taulextable
prettycompilerfront
testsCompile/test11a testsCompile/testall testsCompile/testopt 
tests/bug7 tests/checking tests/myseq tests/point tests/randomphrase tests/test11 tests/test20 tests/testencoding tests/testfileio tests/testmodules tests/testprocess tests/testseq tests/wordfreq 
uses stdlib
exports baseTypeCheck doc genLR1 profile taulextable tools  uniqueids wordgraph testall



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

use taulextable

use doc

use seq.char

use genLR1

use baseTypeCheck

use pretty

use testall

Function entrypoint(s:UTF8) UTF8
 let args=towords.s
 let arg=[first.args]
 let arg2= if length.args > 1 then [args_2] else ""
 HTML.if arg="lextable" then getlextable
 else if arg="testprofile" then 
 testprofile.arg2
 else if arg="doclibrary" then 
 doclibrary.arg2
  else if arg="htmlcode" then 
 doclibrary.arg2
  else if arg="callgraphbetween" then
   let otherargs= if  char1."/" /in decodeword.last.args then  args >> 1 else  args
   callgraphbetween([args_2],otherargs << 2)
  else if arg="callgraphwithin" then
   let otherargs= if  char1."/" /in decodeword.last.args then  args >> 1 else  args
   callgraphwithin([args_2],otherargs << 2)
 else if arg="pretty" then
   let otherargs=    
     if length.args > 3 /and args_-2=first."." then args >> 3 else  args
    pretty(otherargs << 1,"junk") 
  else if arg="taugrammar" then
  gentau2
    else if arg="testall" then
   testall
   else if arg="baseTypeCheck" then 
 baseTypeCheck.arg2
   else if arg="test3" then test3.arg2
  else  "unknown arg"+args
 


Function test3(lib:seq.word) seq.word 
totext(compilerfront("text",lib),"junk"
,[rename("seq.T:findelement(T,seq.T) seq.T","lookup",[2,1])
,rename("set.symdef:findelement(symdef,set.symdef) set.symdef","lookup",[2,1])
,rename("set.passtypes:findelement(passtypes,set.passtypes) set.passtypes","lookup",[2,1])
,rename("set.passsymbols:findelement(passsymbols,set.passsymbols) set.passsymbols","lookup",[2,1])
,rename("set.typeentry:findelement(typeentry,set.typeentry) set.typeentry","lookup",[2,1])
]
)





