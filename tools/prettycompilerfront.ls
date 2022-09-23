Module prettycompilerfront

use file

use seq.file

use format

use libllvm

use compilerfrontT.libllvm

use set.modref

use mytype

use seq.mytype

use pretty

use reconstructUses

use seq.rename

use standard

use set.arc.symbol

use graph.symbol

use otherseq.symbol

use set.symbol

use symbol2

use seq.symdef

use set.symdef

use textio

use otherseq.seq.word

use stack.seq.word

function key(p:seq.word)word
if isempty.p then first."?"
else if first.p ∈ " /keyword"then p_2 else first.p

Function transform(input:seq.file, o:seq.word, target:seq.word, modrename:seq.word, parseit:boolean
, reorguse:boolean, html:boolean, noindex:boolean)seq.file
let modrenames = modrename
let m = 
 if parseit then compilerFront:libllvm("text", input)else empty:midpoint
let srctext = 
 if parseit then totext.m
 else
  for acc = empty:seq.seq.word, i ∈ input do
   if ext.fn.i ∈ "libinfo"then acc else acc + breakparagraph.data.i
  /for(acc)
let exported = exportedmodref.m
let dict = for uses = empty:set.symbol, sd ∈ toseq.prg.m do uses + sym.sd /for(uses)
let directory = if isempty.target then"tmp"else target
for txt = empty:seq.seq.word
, modtext = ""
, uses = empty:seq.seq.word
, p ∈ srctext + "Module ?"
do
 if isempty.p then next(txt, modtext, uses)
 else
  let key = key.p
  if subseq(p, 1, 2) = "parts="then next(txt, modtext, uses)
  else if first.p ∈ "use"then
   next(txt
   , if reorguse then modtext else modtext + " /p  /keyword" + p
   , uses + p << 1
   )
  else if key ∈ "Function function type"then
   next(txt, modtext + " /p" + if parseit then p else pretty.p, uses)
  else if key ∈ "Module module"then
   if key.modtext ∉ "Module module"then next(txt + modtext, p, empty:seq.seq.word)
   else
    let modname = modtext_2
    if not.reorguse then next(txt + modtext, p, empty:seq.seq.word)
    else
     let idx = includecomment.modtext
     let uselist0 = 
      if parseit then
       for uselist = empty:seq.seq.word, ref4 ∈ toseq.reconstruceUses(m, modname, dict, exported, uses)do uselist + print.ref4 /for(uselist)
      else uses
     let uselist = 
      if isempty.modrenames then uselist0
      else
       for uselist = empty:seq.seq.word, u ∈ uselist0 do uselist + ([rename(modrenames, u_2)] + u << 2)/for(uselist)
     let formatedModuleText = 
      for newuses = "", ref ∈ sortuse(uselist, "")do newuses + " /p  /keyword use" + ref /for("Module" + rename(modrenames, modname) + subseq(modtext, 3, idx - 1) + newuses
      + modtext << (idx - 1))
     next(txt + formatedModuleText, p, empty:seq.seq.word)
  else
   next(txt
   , modtext + " /p"
   + if html then if key ∈ "Export"then" /keyword" + p else p
   else escapeformat.p
   , uses
   )
/for(if html then
 for maintxt = "", header = "", M ∈ txt do
  if key.M ∉ "Module module"then next(maintxt + M + " /p", header)
  else
   let modname = M_2
   let indextxt = 
    if noindex then""else" /< noformat <hr id=$(dq.[modname])>  />"
   next(maintxt + indextxt + " /keyword $(M) /p"
   , header
   + "<a href=$(dq.[merge.["#"_1, modname]])> $([modname])</a>"
   )
 /for([file(o
 , if noindex then maintxt else" /< noformat $(header)+ />" + maintxt
 )
 ])
else
 let para = 
  if reorguse then"reorguse"else""/if
  + if parseit then"parseit"else""/if
  + for txt2 = "", x ∈ input do txt2 + " /br" + fullname.fn.x /for(txt2)
 for files = empty:seq.file
 , summary = "inputs" + para + " /p files created"
 , M ∈ txt
 do
  if subseq(M, 1, 1) ∉ ["Module", "module"]then next(files, summary)
  else
   let modname = M_2
   let fn = filename("+" + directory + modname + ".ls")
   next(files + file(fn, M), summary + " /br" + fullname.fn)
 /for(files + file(o, summary))/if)

* The  /keyword transform cmd takes a list of input source files. The output can be for each module creates a file
 containing the pretty printed module in the directory <Tau>/tmp or the output can be an html file.The html format is
 specified with the  /keyword html flag.Addition parameter allows for different variants. 

* transform helloworld/helloworld.ls
 /br transform helloworld/helloworld.ls flags=reorguse
 /br transform  +built HelloWorld.libsrc	 stdlib.libinfo flags=parseit
 /br transform  +built HelloWorld.libsrc	 stdlib.libinfo flags=parseit reorguse

* This first variant does not require the source to be sematicaly correct but the syntax must be correct. It does not
 change the order of the paragraphs.

* The second is like the first except that it moves the use paragraphs to the beginning of the module, removes duplicates
 , and sorts them.

* The third is like the first but requires correct semantics. This allows some additional transformations such as"
 not(a=b)"to become"a /ne b"

* If the option"flags=html"is used and html file is produced with an index of modules.This option is useful for
 examining source code. For example </ block transform htmlcode+built core.libsrc flags=html/> If the option"
 flags=html noindex"is used then no index is included. This final form is useful for producing documentation with
 imbedded Tau code.

Function unusedsymbols(input:seq.file, o:seq.word, flags:seq.word)seq.file
let m = compilerFront:libllvm("text", input)
let dict = for uses = empty:set.symbol, sd ∈ toseq.prg.m do uses + sym.sd /for(uses)
let templates = 
 for acc = templates.m, sym ∈ toseq.dict do
  if isabstract.module.sym ∧ isempty.getCode(templates.m, sym)then acc + symdef(sym, empty:seq.symbol, 0)
  else acc
 /for(acc)
let roots = 
 for acc = empty:set.symbol, sd ∈ toseq.prg.m do
  if name.sym.sd ∈ "entrypoint" ∧ %.resulttype.sym.sd = "UTF8"then acc + sym.sd
  else acc
 /for(acc)
let a2 = closeuse(empty:set.symbol, roots, prg.m, templates, dict)
let flag = "generated"_1 ∈ flags
let a3 = 
 for acc = empty:set.symbol, prg = empty:seq.symdef, sym ∈ toseq(dict \ a2)do
  let b = getSymdef(prg.m, sym)
  if xor(not.isempty.b ∧ paragraphno.b_1 ≠ 0, flag)then next(acc + sym, prg + b_1)
  else next(acc, prg)
 /for(if"all"_1 ∉ flags then
  for arcs = empty:set.arc.symbol, sd ∈ prg do
   for arcs2 = arcs, sy ∈ toseq(asset.code.sd ∩ acc - sym.sd)do arcs2 + arc(sym.sd, sy)/for(arcs2)
  /for(let g = newgraph.toseq.arcs
  {assert false report %n.toseq((nodes.g \ asset.sources.g))}acc \ (nodes.g \ asset.sources.g))
 else acc /if)
let out = 
 for acc = empty:seq.seq.word, sym ∈ toseq.a3 do acc + %.sym /for("Unused symbols for roots" + %.toseq.roots + " /p" + %n.alphasort.acc)
[file(o, out)]

* The  /keyword unusedsymbols cmd analyzes code for unused functions. This can be usefull in determining unused code
 . It forms of the function call graph for the program. It then looks for any any sources in the call graph that are not the
 entry point of the program and list them. Any functions that are generated from type definitions are also removed. 
 The behavior can be modified with flags. If the flag  /keyword all is included the all unused functions are listed and
 not just the roots. If the flag  /keyword generated is included only the generated from type definitions are included
 . Here is an example
 /< block tau tools unusedsymbols+built tools.libsrc stdlib.libinfo common  />

type rename is symtext:seq.word, newname:seq.word, paraorder:seq.int, sym:symbol

Export type:rename

Function rename(symtext:seq.word, newname:seq.word, paraorder:seq.int)rename rename(symtext, newname, paraorder, Lit.0)

function =(a:rename, b:rename)boolean sym.a = sym.b

rename("typepass:change(int, int)int", "change2", [2, 1])

function lookup(a:seq.rename, sym:symbol)seq.rename lookup(a, rename("", "", empty:seq.int, sym))

function rename(renames:seq.word, name:word)word
let i = findindex(name, renames)
if i > length.renames then name else renames_(i + 2)

function totext(result1:midpoint)seq.seq.word
let renames = empty:seq.rename
let src = src.result1
let acc4 = 
 for acc4 = src, sd ∈ toseq.prg.result1 do
  if paragraphno.sd = 0 then acc4
  else
   let c = code.sd
   {assert name.sym.sd /nin"xxx"report print.c}
   let tmp = if Optionsym = last.c then c >> 2 else c
   let newtext = 
    getheader.src_(paragraphno.sd) >> 1
    + for acc = "", stk = empty:stack.seq.word, last = c_1, sym ∈ tmp << 1 do
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
   replace(acc4, paragraphno.sd, pretty.newtext)
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
   else p
  next(acc, modtext + t, beforeModule)
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
 let wd = worddata.sym
 if first.wd = first.dq then push(stk, dq + subseq(wd, 2, length.wd - 1) + dq)
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
else if nopara.sym = 2 ∧ name.sym ∈ "$"then
 let args = top(stk, 2)
 let new = 
  if first.args_2 ∈ dq ∧ first.args_1 ∈ dq then args_1 >> 1 + args_2 << 1
  else args_1 >> 1 + "$" + "(" + args_2 + ")" + dq
 push(pop(stk, 2), new)
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

Function closeuse(done:set.symbol, toprocess:set.symbol, prg:set.symdef, templates:set.symdef, dict:set.symbol)set.symbol
let new0 = 
 for acc = empty:seq.symbol, sym ∈ toseq.toprocess do acc + getCode(prg, sym)/for(acc)
let new1 = 
 for acc = empty:seq.symbol, sym ∈ toseq.asset.new0 do
  if isspecial.sym ∨ iswords.sym ∨ isInternal.sym ∨ islocal.sym ∨ name.module.sym ∈ "$for"
  ∨ isBuiltin.sym
  ∨ isIntLit.sym
  ∨ isRealLit.sym then
   acc
  else acc + sym
 /for(asset.acc \ done)
let new2 = requires(new1, templates, dict, true) \ done ∪ new1
if isempty.new2 then done else closeuse(done ∪ toprocess, new2, prg, templates, dict)

function xor(a:boolean, b:boolean)boolean if a then not.b else b

function %(a:arc.symbol)seq.word %.tail.a + %.head.a 