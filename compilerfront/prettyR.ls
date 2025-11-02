Module prettyR

use UTF8

use seq.mytype

use seq1.prettyR

use seq.prettyR

use stack.prettyR

use prettySupport

use standard

use seq.symbol

use set.symbol

use symbol1

use seq1.symlink

use set.symlink

use textio

use seq1.word

Export type:symlink

Export file(symlink) seq.word

Export id(symlink) seq.word

Export getheader(s:seq.word) seq.word {From prettySupport}

Export formatHeader(p:seq.word) seq.word

Export showZ(out:seq.word) seq.word {From prettySupport}

Export width(seq.word) int {From prettySupport}

Export maxwidth int {From prettySupport}

type prettyR is prec:int, width:int, text:seq.word

function prettyR(s:seq.word) prettyR prettyR(0, width.s, s)

function checkNot(sym:symbol) seq.symbol
{for converting not (a = b) into a ≠ b and the like}
let paratypes = paratypes.sym,
if n.paratypes ≠ 2 then empty:seq.symbol
else
 let i = findindex("= ∈ < >", name.sym),
 if i > 4 then empty:seq.symbol
 else
  let newname = "≠ ∉ ≥ ≤" sub i,
  [symbol(internalmod, [newname], [paratypes sub 1, paratypes sub 2], typeboolean)]

Function x345(a:seq.word) seq.word a + ":(345 - 346)"

Function pretty(syms:seq.symbol, links:set.symlink, changein:boolean) prettyR
if isempty.syms then prettyR(0, 0, "")
else
 let change = if changein then if isempty.links then 2 else 4 else 0
 for stk = empty:stack.prettyR, sym0 = Lit.0, skip = true, nextsym ∈ syms + Lit.0
 do
  if skip then next(stk, nextsym, false)
  else if not.isspecial.kind.nextsym ∧ kind.sym0 = kwords ∧ kind.nextsym = kmakereal then next(push(stk, prettyR.worddata.sym0), nextsym, true)
  else
   let checkNot = if nextsym = NotOp then checkNot.sym0 else empty:seq.symbol
   let newskip = if isempty.checkNot then false else true
   let sym = if isempty.checkNot then sym0 else checkNot sub 1,
   let newstk =
    let kind = kind.sym,
    if kind = kdefine ∧ not.isempty.stk then
     {let id =}
     let stk0 = reduce(stk, change)
     let exp = top.stk0,
     let new = "/keyword let:([name.sym]) =",
     push(pop.stk0, prettyR(0, width.new + width.exp, new + addblock.exp))
    else if kind = kstart then push(stk, prettyR."")
    else if kind = kbr then reduce(stk, change)
    else if kind = kexit then
     let stk1 = reduce(stk, change)
     let thenpart = top.stk1
     let ifpart = undertop(stk1, 1)
     let overallwidth = width.ifpart + width.thenpart + 5,
     let tmp =
      if overallwidth > maxwidth then prettyR(0, 10000, text.ifpart + "then" + addblock.thenpart)
      else
       {if overallwidth > maxwidth then prettyR (0, 10000, text.ifpart+" then
       /br"+text.thenpart) else}
       prettyR(0, overallwidth, text.ifpart + "/keyword then" + text.thenpart),
     push(
      push(pop(stk1, 2), tmp)
      , prettyR(10, 7, if isempty.text.undertop(stk1, 2) then "/keyword if" else "/keyword else if")
     )
    else if kind = kendblock ∧ n.toseq.stk ≥ 2 then
     let stk1 = reduce(stk, change)
     let stk2 = if width.top.stk1 < 10000 then stk1 else push(pop.stk1, prettyR.addblock.top.stk1),
     push(stk2, prettyR(10, 7, "/keyword else"))
    else if kind = kint then push(stk, prettyR.[name.sym])
    else if kind = kwords then push(stk, prettyR."<* literal /tag:(dq.escapeformat.worddata.sym) *>")
    else if name.sym ∈ "$assert" then
     let reportpart = reduce(stk, change)
     let assertpart = reduce(pop.reportpart, change),
     if width.top.reportpart + 14 > maxwidth then
      push(
       pop.assertpart
       , prettyR(
        0
        , 10000
        , "/keyword assert:(addblock.top.assertpart) /keyword report:(addblock.top.reportpart)"
       )
      )
     else
      push(
       pop.assertpart
       , prettyR."/keyword assert:(text.top.assertpart) /keyword report:(text.top.reportpart)"
      )
    else if nopara.sym = 0 then
     let tmp = if kind.sym ∈ [kother, kcompoundname] then href(sym, links) else compoundName.sym,
     push(stk, prettyR.tmp)
    else if nopara.sym = 1 ∧ name.sym ∈ "(" then
     if changein then stk
     else
      let stk1 = reduce(stk, 0),
      push(pop.stk1, prettyR(0, width.top.stk1 + 2, "(:(text.top.stk1))"))
    else if nopara.sym = 1 ∧ name.sym ∈ "{" then
     {comment in header}
     push(pop.stk, prettyR."<* comment /tag {:(subseq(text.top.stk, 5, n.text.top.stk - 2))} *>")
    else if nopara.sym = 1 ∧ name.sym ∈ "-" then
     {unary minus}
     let stk1 = reduce(stk, if prec.top.stk > 2 then {add ()} change + 1 else change),
     push(push(push(pop.stk1, prettyR.""), top.stk1), prettyR(2, 1, "-"))
    else if name.sym ∈ "%" ∧ nopara.sym = 1 ∧ catStringOp = nextsym ∧ isString.top.pop.reduce(stk, change) then
     {handle"...:(%.exp)..."}
     let stk1 = reduce(stk, change)
     let txt = text.top.stk1,
     push(pop.stk1, prettyR."<* literal /tag:(dq(":" + "(:(txt))")) *>")
    else if nopara.sym = 1 ∧ prec.top.stk < 3 ∧ kind.sym ≠ ksequence ∧ hassimplename.sym then
     {name.arg format}
     let stk1 = reduce(stk, change),
     push(push(push(pop.stk1, prettyR.href(sym, links)), top.stk1), prettyR(2, 0, "."))
    else if name.sym ∈ "{" ∧ nopara.sym = 2 then
     {comment on expression}
     let expstk = reduce(stk, change)
     let comment = text.top.pop.expstk
     let comment1 = "{:(subseq(comment, 5, n.comment - 2))}",
     let new =
      if width.comment1 + width.top.expstk > maxwidth then prettyR(0, 10000, comment1 + "/br:(text.top.expstk)")
      else prettyR(comment1 + text.top.expstk),
     push(pop(expstk, 2), new)
    else
     let opprec = if nopara.sym = 2 then opprec.name.sym else 0,
     if opprec > 0 then
      {binary op}
      let new =
       if name.sym ∈ "$mergecode" then prettyR(opprec, 10000, "")
       else if name.sym ∈ "+-" then prettyR(opprec, 3, "/sp:(href(sym, links)) /sp")
       else prettyR(opprec, width.[name.sym], href(sym, links))
      let stk1 =
       if prec.top.stk ≠ 0 then
        let tmp = if prec.top.stk = 2 ∧ opprec = 1 then false else prec.top.stk ≥ opprec,
        reduce(stk, if tmp ∧ change > 0 then {add ()} change + 1 else change)
       else stk,
      let t = pop.stk1,
      if sym = catStringOp ∧ isString.top.t then
       {handle adding back in...:()... in strings}
       if isString.top.stk1 then
        let ttext = text.top.t,
        if ttext sub (n.ttext - 3) ∈ ":" ∧ (text.top.stk1) sub 6 ∈ "(" then push(stk1, prettyR(opprec."+" sub 1, 1, "/sp+/sp"))
        else push(pop.t, prettyR(text.top.t >> 2 + text.top.stk1 << 4))
       else push(pop.t, prettyR(text.top.t >> 2 + ":" + "(:(removeclose.text.top.stk1)):(dq) *>"))
      else if prec.top.t ∈ [0, opprec] then push(stk1, new)
      else
       let tmp = if opprec = 2 ∧ prec.top.t = 1 then false else prec.top.t > opprec,
       push(push(reduce(t, if tmp ∧ change > 0 then {add ()} change + 1 else change), top.stk1), new)
     else
      {create arg list}
      for stk1 = stk, args = empty:seq.prettyR, e ∈ constantseq(nopara.sym, 1)
      do
       let stkt = reduce(stk1, change),
       next(pop.stkt, [top.stkt] + args),
      if name.sym ∈ "$fortext" then
       let whileexp = text.args sub (n.args - 2)
       let accNames = {remove quotes} subseq(text.args sub n.args, 6, n.text.args sub n.args - 3)
       for acc6 = empty:stack.prettyR, i = 1, name ∈ accNames
       do
        if i = n.accNames ∧ name ∈ "." then {for has no sequence} next(acc6, i + 1)
        else
         let tmp = prettyR(%.name + (if i = n.accNames then "∈" else "=") + text.args sub i),
         next(if i = 1 then push(acc6, tmp) else push(push(acc6, tmp), prettyR(15, 2, ",")), i + 1)
       let accums = "/keyword for:(addblock.top.reduce(acc6, change))",
       let forexp =
        if width.args + width.accums > maxwidth then
         prettyR(
          0
          , 10000
          , accums
           + (if whileexp = "true" then "" else "/br /keyword while:(whileexp)")
           + "/br /keyword do:(addblock.args sub (n.args - 1))"
         )
        else
         prettyR(
          accums
           + (if whileexp = "true" then "" else "/keyword while:(whileexp)")
           + "/keyword do:(addblock.args sub (n.args - 1))"
         ),
       push(stk1, forexp)
      else
       let w = width."():(compoundName.sym)"
       let plist = merge(args, change),
       if kind.sym = ksequence then push(stk1, prettyR(0, width.plist + 2, "[:(addblock.plist)]"))
       else push(stk1, prettyR(0, w + width.plist, href(sym, links) + "/tag (" + addblock.plist + ")")),
   next(newstk, nextsym, newskip)
 let tmp = top.reduce(stk, change),
 let tmp2 = removeclose.text.tmp,
 prettyR(0, width.tmp, tmp2)

function addblock(s:prettyR) seq.word
if width.s < 10000 then text.s else "<* block:(text.s) *>"

function merge(s:seq.prettyR, change:int) prettyR
let op = prettyR(15, 2, ",")
for acc = push(empty:stack.prettyR, s sub 1), p ∈ s << 1
do push(push(acc, p), op),
top.reduce(acc, change)

function %(r:prettyR) seq.word "{:(prec.r)}:(text.r)"

function reduce(stk:stack.prettyR, changein:int) stack.prettyR
let change = changein > 1
let addparenthesis = changein ∈ [3, 5]
let html = changein > 3,
if prec.top.stk = 0 then stk
else
 for acc1 = stk, args = empty:seq.prettyR, ops = empty:seq.prettyR, width = 0
 while prec.top.acc1 ≠ 0
 do
  let tmp = top(acc1, 2),
  next(
   pop(acc1, 2)
   , [tmp sub 1] + args
   , [tmp sub 2] + ops
   , width + width.tmp sub 1 + width.tmp sub 2
  )
 let firstarg =
  if change ∧ prec.ops sub 1 = 1 ∧ prec.top.acc1 > 1 then "(:(text.top.acc1))"
  else text.top.acc1
 for text = firstarg, big = firstarg, width2 = width.text.top.acc1, i = 1, e ∈ args
 do
  let op = ops sub i
  let addbr = if blockIsLast.big ∨ text.op = "." then "" else "/br",
  if prec.op = mergecodePrec ∧ i = n.ops then
   next(
    addcomma(if change then removeclose.text else text) + text.op + text.e
    , addcomma(if change then removeclose.big else big) + addbr + text.op + text.e
    , width2 + width.e + width.op
    , i + 1
   )
  else if prec.op = 1 ∧ i < n.ops ∧ change then
   next(
    "(:(text):(text.op):(text.e))"
    , if isempty.big then text.op + text.e else "(:(big) /br:(text.op):(text.e))"
    , width2 + width.e + width.op
    , i + 1
   )
  else
   let tmp1 =
    if html ∧ prec.op = 1 ∧ "sub" sub 1 ∈ text.op then "/tag <sub>:(text.e) /tag </sub>"
    else text.op + text.e,
   next(
    text + tmp1
    , (if isempty.big then big else big + addbr) + text.op + text.e
    , width2 + width.e + width.op
    , i + 1
   )
 let finaltext = if width2 < maxwidth then text else big
 let finalwidth = if width2 < maxwidth then width2 else 10000,
 let new =
  if change ∧ addparenthesis ∧ prec.top.stk ≠ mergecodePrec then prettyR(0, width2 + 2, "(:(finaltext))")
  else prettyR(0, finalwidth, finaltext),
 push(pop.acc1, new)

function width(s:seq.prettyR) int
for width = 0, e ∈ s do width + width.e,
width

function catStringOp symbol
symbol(moduleref("* seq", typeword), "+", [seqof.typeword, seqof.typeword], seqof.typeword)

function isString(b:prettyR) boolean
text.b << (n.text.b - 2) = dq + "*>" ∧ subseq(text.b, 1, 4) = "<* literal /tag:(dq)"

Function id(sym:symbol) seq.word
for txt = "", type ∈ types.sym do txt + ":" + %.type,
if issimplename.sym then [name.sym] + txt else [name.sym] + ":" + txt

function href(sym:symbol, links:set.symlink) seq.word
if isempty.links then compoundName.sym
else
 let symid = id.sym
 let find = findelement2(links, symlink(symid, ""))
 for match = symlink("", "", 0), e ∈ toseq.find
 while firstT.match = 0
 do
  if symid = id.e then e
  else if firstT.e < n.id.e ∧ firstT.e < n.symid then
   {for when id.e has a T. The T must be replaced with the actual type}
   let T = subseq(symid, firstT.e, firstT.e + findindex(symid << firstT.e, ":" sub 1) - 1)
   for neweid = "", w ∈ id.e
   do if w ∈ "T" then neweid + T else neweid + w,
   if neweid = symid then e else match
  else match,
 let result =
  if firstT.match ≠ 0 then
   let tmp = if isempty.file.match then "" else "/tag:(file.match)",
   "/tag <a /sp href =:(dq.":(tmp) /tag #:(id.match)") >:(compoundName.sym) /sp /tag </a>"
  else compoundName.sym,
 result

function %(s:symlink) seq.word id.s + file.s + %.firstT.s

Function pretty(
header:seq.word
, code:seq.symbol
, syms:set.symlink
, change:boolean
) seq.word
let body = pretty(code, syms, change)
let h = if width.header < maxwidth then header else formatHeader.header,
if width.header + width.body < maxwidth then h + text.body else h + "/br" + text.body

Function escapeformat(in:seq.word) seq.word
for result = [escapeformat], w ∈ in
do
 if w
 ∈ "/br
 /p
 /row"
 ∧ n.result > 1 then result + escapeformat + "/br" + escapeformat + w
 else result + w,
result + escapeformat

Function compoundNameType mytype typeref."internal internal:"

function hassimplename(s:symbol) boolean
if resulttype.s = compoundNameType then false else issimplename.s

function compoundName(s:symbol) seq.word
if resulttype.s = compoundNameType then towords(emptyUTF8 + decodeword.name.s)
else fullname.s

--------------------

Function symlink(id:seq.word, file:seq.word) symlink
symlink(id, file, findindex(id, "T" sub 1))

type symlink is id:seq.word, file:seq.word, firstT:int

Function >2(a:symlink, b:symlink) ordering
let m = min(firstT.a, firstT.b) - 1,
subseq(id.a, 1, m) >1 subseq(id.b, 1, m)

Function >1(a:symlink, b:symlink) ordering
let m = min(firstT.a, firstT.b) - 1,
subseq(id.a, 1, m) >1 subseq(id.b, 1, m) ∧ id.a >1 id.b ∧ file.a >1 file.b

use token 
