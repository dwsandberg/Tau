Module prettycompilerfront

use UTF8

use bits

use format

use libraryModule

use pretty

use standard

use symbol2

use textio

use seq.byte

use otherseq.char

use seq.char

use seq.mytype

use seq.rename

use seq.symbol

use seq.symbolref

use seq.seq.symbolref

use otherseq.seq.word

use stack.seq.word

type rename is symtext:seq.word, newname:seq.word, paraorder:seq.int, sym:symbol

Export type:rename

Function rename(symtext:seq.word, newname:seq.word, paraorder:seq.int)rename rename(symtext, newname, paraorder, Lit.0)

function =(a:rename, b:rename)boolean sym.a = sym.b

rename("typepass:change(int, int)int", "change2", [2, 1])

function lookup(a:seq.rename, sym:symbol)seq.rename lookup(a, rename("", "", empty:seq.int, sym))

function preprocess(a:seq.rename, c:compileinfo)seq.rename
for result = empty:seq.rename, r ∈ a do
 let sym = 
  for acc = empty:seq.symbol, sym ∈ symbolrefdecode.c do if print.sym = symtext.r then acc + sym else acc /for(acc)
 if isempty.sym then result else result + rename(symtext.r, newname.r, paraorder.r, sym_1)
/for(result)

Function totext(result1:compileinfo, directory:seq.word)seq.word
writeModule(totext(result1, empty:seq.rename), directory)

Function Optionsym symbol symbol(internalmod, "option", typeint, seqof.typeword, typeint)

Function totext(result1:compileinfo, directory:seq.word, renames0:seq.rename)seq.word
writeModule(totext(result1, renames0), directory)

Function totext(result1:compileinfo, renames0:seq.rename)seq.seq.word
let renames = preprocess(renames0, result1)
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
for acc = empty:seq.seq.word, modtext = "", p ∈ acc4 do
 if subseq(p, 1, 1) ∈ ["Module", "module", [encodeword.[char.28]]]then
  next(acc + modtext, p)
 else {if subseq(p, 1, 2) = "file("then next(acc, modtext)
  else}
  let t = 
   if subseq(p, 1, 1)
   ∈ [" /keyword", "use", "builtin", "Export"]then
    p
   else if subseq(p, 1, 1) ∈ ["type", "Function", "function"]then pretty.p
   else escapeformat.p
  next(acc, modtext + " /p" + t)
/for(acc)

function newstk(sym:symbol, stk:stack.seq.word, renames:seq.rename)stack.seq.word
if isstart.sym ∨ isexit.sym ∨ isbr.sym then stk
else if name.module.sym ∈ "$int"then push(stk, [name.sym])
else if name.sym = first."let" ∧ length.toseq.stk ≥ 2 then
 let args = top(stk, 2)
 push(pop(stk, 2), args_1 + "(" + args_2 + ")")
else if isdefine.sym ∧ not.isempty.stk then
 push(pop.stk, "let" + [name.sym] + "=(" + top.stk + ")")
else if iswords.sym then 
  let wd=worddata.sym
 if first.wd = first."'" ∧ dq_1 ∉ wd then push(stk, dq + subseq(wd, 2, length.wd - 1) + dq)
 else if first.wd ∈ "'" ∧ length.wd = 3 then push(stk, "dq")else push(stk, wd)
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

function writeModule(modtexts:seq.seq.word, directory:seq.word)seq.word
{OPTION INLINE}
for txt = "", modtext ∈ modtexts do
 if not.isempty.modtext ∧ first.modtext ∈ "Module module"then
  let discard2 = 
   createfile([merge(directory + "/" + modtext_2 + ".ls")], toseqbyte.textformat.modtext)
  txt + " /p" + modtext
 else txt
/for(txt)

/use libraryModule

/use seq.seq.word

/use otherseq.char

/use seq.char

Function prettybyfile(libname:seq.word, targetdir:seq.word)seq.word
let z = getlibrarysrc.libname + "file(dummy)"
for txt = "", last = 0, idx = 1, k ∈ z do
 if subseq(k, 1, 2) = "file("then
  if last = 0 then next(txt, idx, idx + 1)
  else
   let zz = prettyfile(true, "", subseq(z, last + 1, idx - 1)) << 1
   let filename = extractfilename.z_last
   if isempty.filename then next(txt, idx, idx + 1)
   else
    let discard = createfile(targetdir + "/" + filename, toseqbyte.textformat.zz)
    next(txt + zz, idx, idx + 1)
 else next(txt, last, idx + 1)
/for(txt)

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