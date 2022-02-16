#!/bin/sh tau stdlib tools callgraphwithin stdlib interpreter  

#!/bin/sh tau stdlib tools doclibrary tools

#!/bin/sh tau stdlib tools callgraphbetween stdlib standard inputoutput

#!/bin/sh tau stdlib tools pretty stdlib tausupport bits bitstream format set textio stack encoding otherseq process 
real seq standard UTF8 words xxhash

#!/bin/sh tau stdlib tools test3 stdlib

tau stdlib tools test3 wtest1

Module tools

Library tools bandeskopf barycenter baseTypeCheck doc genLR1 layergraph makeDag prettycompilerfront profile svg2graph taulextable
uses stdlib
exports baseTypeCheck doc genLR1 profile taulextable tools uniqueids wordgraph

* STATE builtin:profile profileinfo profileresult

* only document printbitcodes profile prettylib doc

* usegraph exclude standard seq set otherseq UTF8 real graph

use UTF8

use baseTypeCheck

use compilerfront

use doc

use genLR1

use main2

use pretty

use prettycompilerfront

use profile

use standard

use taulextable

use seq.char

use seq.word

use process.seq.word

use seq.seq.word

Function testprofile(libname:seq.word)seq.word subcompilelib.libname + profileresults."time"

Function entrypoint(s:UTF8)UTF8
let args = towords.s
let arg = [first.args]
let arg2 = if length.args > 1 then[args_2]else""
HTMLformat.if arg = "lextable"then getlextable
else
 {if arg="test112"then test112 else}
 if arg = "testprofile"then testprofile.arg2
 else if arg = "doclibrary"then doclibrary.arg2
 else if arg = "htmlcode"then htmlcode.arg2
 else if arg = "callgraphbetween"then
  let otherargs = if char1."/" ∈ decodeword.last.args then args >> 1 else args
  callgraphbetween(prg.compilerfront("text", {libname}[args_2]), otherargs << 2)
 else if arg = "callgraphwithin"then
  let otherargs = if char1."/" ∈ decodeword.last.args then args >> 1 else args
  callgraphwithin(prg.compilerfront("text", {libname}[args_2]), otherargs << 2)
 else if arg = "pretty"then
  let otherargs = if length.args > 3 ∧ args_(-2) = first."."then args >> 3 else args
  pretty(otherargs << 1, "tmp")
 else if arg = "taugrammarpretty"then gentaupretty
 else if arg = "taugrammar"then gentau
 else if arg = "baseTypeCheck"then
  let p = process.glue({library}arg2, true)
  if aborted.p then message.p else result.p
 else if arg = "resultCheck"then
  let p = process.glue({library}arg2, false)
  if aborted.p then message.p else result.p
 else if arg = "test3"then test3.arg2
 else if arg = "createdoc"then createdoc else"unknown arg" + args

Function test3(lib:seq.word)seq.word
totext(compilerfront("text", lib)
, "tmp"
, [rename("seq.T:findelement(T, seq.T)seq.T", "lookup", [2, 1])
, rename("set.symdef:findelement(symdef, set.symdef)set.symdef", "lookup", [2, 1])
, rename("set.passtypes:findelement(passtypes, set.passtypes)set.passtypes"
, "lookup"
, [2, 1]
)
, rename("set.passsymbols:findelement(passsymbols, set.passsymbols)set.passsymbols"
, "lookup"
, [2, 1]
)
, rename("set.typeentry:findelement(typeentry, set.typeentry)set.typeentry"
, "lookup"
, [2, 1]
)
]
)

function glue(library:seq.word, basetypecheck:boolean)seq.word
let r2 = compilerfront("pass2", library)
if basetypecheck then baseTypeCheck.r2 else checkresults.prg.r2 