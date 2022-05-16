Module main2

use UTF8

use bits

use compilerfront

use file

use format

use libdesc

use standard

use symbol2

use textio

use words

use seq.byte

use otherseq.char

use seq.file

use process.int

use compileTimeT.libllvm

use compilerfrontT.libllvm

use pass2T.libllvm

use seq.modExports

use set.modref

use seq.mytype

use set.mytype

use seq.symbol

use set.symbol

use seq.symbolref

use seq.symdef

use set.symdef

use otherseq.word

use set.word

use process.seq.bits

use encoding.seq.char

use seq.seq.char

use seq.seq.mytype

use process.seq.word

use seq.seq.word

use set.seq.word

use process.seq.seq.word

use seq.seq.seq.word

Function libname(info:midpoint)word extractValue(first.src.info, "Library")_1

function makeentry(input:seq.byte) seq.byte
let entryheader="use standard /p use file /p use fileIO /p use seq.file
/p use process.UTF8
/p
Function entrypoint(args:UTF8)UTF8
/br let p=process.entrypoint2(args)
/br if aborted.p then
/br   finishentry.[file($(dq."error.html"),message.p)] 
/br else  result.p 
/p function entrypoint2(args0:UTF8)UTF8
/br let args = towords.args0 
/br let input=getfiles.args
/br let cmd= first.args  /br finishentry."
for acc = "", modname = "?"_1, mods = "", p ∈ breakparagraph.input do
 if subseq(p, 1, 1) = "Function" ∧ subseq(p, 3, 8) = "(input:seq.file"then
  let idx = findindex(")"_1, p)
  next(for para = ""
  , name = ", "_1
  , last = ", "_1
  , type = ""
  , w ∈ subseq(p, 10, idx)
  do
   if w ∈ ", )"then
    next(para
    + if type = "seq.word"then", extractValue(args, $(dq.[name]))"
    else if type = "boolean"then
     ", first.$(dq.[name])∈ extractValue(args, $(dq."b="))"
    else", ?"
    , name
    , w
    , ""
    )
   else if last ∈ ":"then next(para, name, last, type + w)
   else if last ∈ ", "then next(para, w, w, "")else next(para, name, w, type)
  /for(acc + " /br else if cmd /in $(dq.subseq(p, 2, 2))then $(subseq(p, 2, 2))(input $(para))")
  , modname
  , mods + modname
  )
 else if length.p > 1 ∧ p_1 ∈ "Module"then next(acc, p_2, mods)
 else next(acc, modname, mods)
/for(let uses = 
 for uses = "", u ∈ toseq.asset.mods do uses + "use" + u + " /p"/for(uses)
[tobyte.10, tobyte.10]
+ toseqbyte.textformat(uses + entryheader + acc << 2 + " /br else empty:seq.file"))

Function libsrc(input:seq.file, uses:seq.word, exports:seq.word, o:seq.word)seq.file
let Library = subseq(o, 1, 1)
for acc = empty:seq.byte, names = "parts=", f ∈ input do
 if ext.fn.f ∈ "ls libsrc"then next(acc + tobyte.10 + tobyte.10 + data.f, names + fullname.fn.f)
 else next(acc, names)
/for(let firstpart = 
 if isempty.exports then
  toseqbyte.toUTF8(names + "uses=$(uses)exports=$(exports)Library=$(Library)")
 else
  let entrypointname = merge(Library + "$EP")
  toseqbyte.toUTF8(names + "uses=$(uses)exports=$(exports + entrypointname)Library=$(Library)")
  + tobyte.10
  + tobyte.10
  + toseqbyte.toUTF8("Module" + entrypointname)
  + makeentry.acc
[file(filename(Library + ".libsrc"), firstpart + acc)])

Function subcompilelib(allsrc:seq.seq.word)seq.bits
{OPTION PROFILE}
let uses = extractValue(first.allsrc, "uses")
let dependentlibs = dependentinfo:libllvm(uses)
let m = compilerfront2:libllvm("all", allsrc, dependentlibs)
compilerback2(prg.m, libmods.m, typedict.m,  extractValue(first.allsrc, "Library")_1, uses, dependentlibs)

Function stdlib(input:seq.file)seq.file
let info = breakparagraph.data.first.input
let libname = extractValue(first.info, "Library")
let p = process.subcompilelib.info
[if aborted.p then
 file("error.html", "COMPILATION ERROR in libray:" + libname + EOL + message.p)
else file(filename(libname + ".bc"), result.p)
]

Function astext(info:midpoint)seq.seq.word
for acc = empty:seq.seq.word, p ∈ toseq.prg.info do acc + [print.sym.p + print.code.p]/for(acc)

Function compilerFront:libllvm(option:seq.word, allsrc:seq.seq.word)midpoint
{OPTION PROFILE }
let libinfo = dependentinfo:libllvm(extractValue(first.allsrc, "uses"))
let m = compilerfront2:libllvm(option, allsrc, libinfo)
m

Function modsE(ci:midpoint)seq.modExports libmods.ci

Export prg(ci:midpoint)set.symdef

function callfunc:libllvm(ctsym:symbol, typedict:typedict, stk:seq.int)seq.int callfunc(ctsym, typedict, stk)

_______________

Export type:libllvm

type libllvm is a:int

function dependentinfo:libllvm(dependentlibs:seq.word)midpoint dependentinfo.dependentlibs 