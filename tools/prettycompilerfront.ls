Module prettycompilerfront

use UTF8

use bits

use format

use libraryModule

use pretty

use standard

use symbol2

use seq.byte

use otherseq.char

use seq.char

use seq.mytype

use seq.rename

use seq.symbol

use seq.symbolref

use otherseq.word

use seq.seq.symbolref

use otherseq.seq.word

use seq.seq.word

use stack.seq.word

type rename is symtext:seq.word, newname:seq.word, paraorder:seq.int, sym:symbol

Export type:rename

Function rename(symtext:seq.word, newname:seq.word, paraorder:seq.int)rename rename(symtext, newname, paraorder, Lit.0)

function =(a:rename, b:rename)boolean sym.a = sym.b

rename("typepass:change(int, int)int", "change2", [2, 1])

function lookup(a:seq.rename, sym:symbol)seq.rename lookup(a, rename("", "", empty:seq.int, sym))

function rename(renames:seq.word, name:word)word
let i = findindex(name, renames)
if i > length.renames then name else renames_(i + 2)

Function transform(cinfo:compileinfo, library:seq.word, modrename:seq.word)seq.seq.word
let result1 = totext.cinfo
for txt = empty:seq.seq.word, modlist = "", libloc = 1, idx = 1, c ∈ result1 do
 if subseq(c, 1, 1) = "use"then
  let newname = rename(modrename, c_2)
  next(txt + replace(c, 2, newname), modlist, libloc, idx + 1)
 else if subseq(c, 1, 1) = "Module" ∨ subseq(c, 1, 1) = "module"then
  let newname = rename(modrename, c_2)
  next(txt + replace(c, 2, newname), modlist + newname, libloc, idx + 1)
 else if libloc = 1 ∧ subseq(c, 1, 1) = "Library"then next(txt + c, modlist, idx, idx + 1)
 else next(txt + c, modlist, libloc, idx + 1)
/for(replace(txt, libloc, fixlibclause(txt_libloc, modlist, modrename)))


function fixlibclause(p:seq.word, modlist:seq.word, modrename:seq.word)seq.word
p

let b = break(p, "uses exports", true)
assert first.last.b ∈ "exports"report"Library clause format"
for txt = "Library" + modlist + " /br" + b_2 + " /br exports"
, e ∈ last.b << 1
do
 txt + rename(modrename, e)
/for(txt)

Function totext(result1:compileinfo)seq.seq.word
let renames = empty:seq.rename
let symdecode = symbolrefdecode.result1
let src = src.result1
let acc4 = 
 for acc4 = src, c ∈ code.result1 do
  let paragraphno = value.symdecode_(toint.c_2)
  if paragraphno = 0 then acc4
  else
   let tmp = if Optionsym = symdecode_(toint.last.c)then c >> 2 else c
   let newtext = 
    getheader.src_paragraphno >> 1
    + for acc = "", stk = empty:stack.seq.word, last = symdecode_(toint.c_3), r ∈ tmp << 3 do
     let sym = symdecode_(toint.r)
     if sym = NotOp ∧ nopara.last = 2 then
      let paratypes = paratypes.last
      let newname = 
       if name.last = "="_1 then"≠"
       else if name.last = "∈"_1 then"∉"
       else if name.last = "<"_1 then"≥"
       else if name.last = ">"_1 then"≤"else[name.last]
      if name.last ≠ newname_1 then
       next(acc, stk, symbol(internalmod, newname, paratypes_1, paratypes_2, typeboolean))
      else next(acc, newstk(last, stk, renames), sym)
     else next(acc, newstk(last, stk, renames), sym)
    /for(top.newstk(last, stk, renames))
   replace(acc4, paragraphno, pretty.newtext)
 /for(acc4)
for acc = empty:seq.seq.word
, modtext = empty:seq.seq.word
, beforeModule = true
, p ∈ acc4 + "Module"
do
 if subseq(p, 1, 1) ∈ ["Module", "module", [encodeword.[char.28]]]then
  next(acc + modtext, [p], false)
 else if subseq(p, 1, 2) = "file("then next(acc + modtext, empty:seq.seq.word, true)
 else
  let t = 
   if subseq(p, 1, 1)
   ∈ [" /keyword", "use", "builtin", "Export"]then
    p
   else if subseq(p, 1, 1) ∈ ["type", "Function", "function"]then pretty.p
   else escapeformat.p
  next(acc, modtext + t, beforeModule)
/for(acc)

Function Optionsym symbol symbol(internalmod, "option", typeint, seqof.typeword, typeint)

function newstk(sym:symbol, stk:stack.seq.word, renames:seq.rename)stack.seq.word
if isstart.sym ∨ isexit.sym ∨ isbr.sym then stk
else if name.module.sym ∈ "$int"then push(stk, [name.sym])
else if name.sym = first."let" ∧ length.toseq.stk ≥ 2 then
 let args = top(stk, 2)
 push(pop(stk, 2), args_1 + "(" + args_2 + ")")
else if isdefine.sym ∧ not.isempty.stk then
 push(pop.stk, "let" + [name.sym] + "=(" + top.stk + ")")
else if iswords.sym then
 let wd = worddata.sym
 if first.wd = first."'" ∧ dq_1 ∉ wd then push(stk, dq + subseq(wd, 2, length.wd - 1) + dq)
 else if first.wd ∈ "'" ∧ length.wd = 3 then push(stk, "dq")
 else if first.wd = first."'" ∧ dq_1 ∈ wd then
  let a = break(subseq(wd, 2, length.wd - 1), dq, false)
  push(stk
  , for txt = dq + first.a, b ∈ a << 1 do txt + dq + "+dq+" + dq + b /for("(" + txt + dq + ")")
  )
 else push(stk, wd)
else if name.sym ∈ "{" ∧ length.toseq.stk ≥ 2 then
 {comment}
 let args = top(stk, 2)
 push(pop(stk, 2), args_1 + args_2)
else if isblock.sym ∧ length.toseq.stk ≥ 3 then
 let args = top(stk, 3)
 push(pop(stk, 3)
 , "if" + args_1 + "then" + args_2 + "else" + args_3 + "/if"
 )
else if name.sym ∈ "assert"then stk
else if name.sym ∈ "makereal" ∧ (top.stk)_2 = "."_1 then stk
else if name.sym = "report"_1 ∧ length.toseq.stk ≥ 3 then
 let args = top(stk, 3)
 push(pop(stk, 3)
 , "assert" + args_1 + "report" + "(" + args_3 + ")(" + args_2
 + ")"
 )
else if nopara.sym = 2 ∧ name.sym ∈ "=+_^∩ ∪ \-* / << >> > < ? ∈ mod ∧ ∨ ≠ ∉ ≥ ≤" ∧ length.toseq.stk ≥ 2 then
 let args = top(stk, 2)
 push(pop(stk, 2), "(" + args_1 + name.sym + args_2 + ")")
else if name.sym = "forexp"_1 ∧ length.toseq.stk ≥ nopara.sym then
 let args = top(stk, nopara.sym)
 let k = (nopara.sym - 3) / 2
 push(pop(stk, nopara.sym)
 , for acc6 = "for", i ∈ arithseq(k, 1, 1)do
  acc6 + args_(i + k) + if i = k then"∈"else"="/if + args_i
  + ", "
 /for(acc6 >> 1
 + if args_(-2) = "true"then""else"while" + args_(-2)/if
 + "do"
 + args_(-3)
 + "/for("
 + args_(-1)
 + ")")
 )
else if length.toseq.stk ≥ nopara.sym then
 if isSequence.sym then
  push(pop(stk, nopara.sym), "[" + addcommas.top(stk, nopara.sym) + "]")
 else
  let xx = lookup(renames, sym)
  if not.isempty.xx then
   push(pop(stk, nopara.sym)
   , if nopara.sym = 0 then newname.xx_1
   else
    let args = top(stk, nopara.sym)
    for acc = newname.xx_1 + "(", i ∈ paraorder.xx_1 do acc + args_i + ", "/for(acc >> 1 + ")")
   )
  else
   push(pop(stk, nopara.sym)
   , if nopara.sym = 0 then fullname.sym
   else fullname.sym + "(" + addcommas.top(stk, nopara.sym) + ")"
   )
else stk

function addcommas(s:seq.seq.word)seq.word
for acc2 = "", t ∈ s do acc2 + t + ", "/for(acc2 >> 1)

function extractfilename(s:seq.word)seq.word
let k = findindex(first.")", s)
if subseq(s, 1, 2) = "file(" ∧ k ≤ length.s then subseq(s, 3, k - 1)
else""

function outname(file:word, targetdir:seq.word)seq.word
let chars = decodeword.file
if chars_1 = char1."/"then
 targetdir + "/" + encodeword(chars << (findindex(char1."/", chars << 1) + 1))
 + ".ls"
else targetdir + "/" + file + ".ls" 