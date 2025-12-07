Module prettyR

use UTF8

use autolink

use seq1.autolink

use set.autolink

use seq.mytype

use seq.prettyR

use seq1.prettyR

use stack.prettyR

use prettySupport

use standard

use seq.symbol

use set.symbol

use symbol1

use textio

use token

use seq1.word

Export getheader(s:seq.word) seq.word{From prettySupport}

Export formatHeader(p:seq.word) seq.word

Export showZ(out:seq.word) seq.word{From prettySupport}

Export width(seq.word) int{From prettySupport}

Export maxwidth int{From prettySupport}

type prettyR is prec:int, width:int, text:seq.word

function prettyR(s:seq.word) prettyR prettyR(0, width.s, s)

function checkNot(sym:symbol) seq.symbol
{for converting not(a = b)into a ≠ b and the like}
let paratypes = paratypes.sym,
if n.paratypes ≠ 2 then empty:seq.symbol
else
 let i = findindex("= ∈ < >", name.sym),
 if i > 4 then empty:seq.symbol
 else
  let newname = "≠ ∉ ≥ ≤" sub i,
  [symbol(internalmod, [newname], [paratypes sub 1, paratypes sub 2], typeboolean)]

Function pretty(syms:seq.symbol, links:set.autolink, changein:boolean) prettyR
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
     let exp = top.stk0
     let widthexp = width.exp
     let head = "// let /keyword:([name.sym])/sp ="
     let totwidth = width.head + widthexp,
     let new =
      head + if totwidth < maxwidth then "/sp:(text.exp)" else "//:(text.exp)/block",
     push(pop.stk0, prettyR(0, totwidth, new))
    else if kind = kstart then push(stk, prettyR."")
    else if kind = kbr then reduce(stk, change)
    else if kind = kexit then
     let stk1 = reduce(stk, change)
     let thenpart = top.stk1
     let ifpart = undertop(stk1, 1)
     let overallwidth = width.ifpart + width.thenpart + 5,
     let tmp =
      if overallwidth > maxwidth then prettyR(0, 10000, text.ifpart + "/sp // then /keyword" + removeclose.addblock.thenpart)
      else prettyR(0, overallwidth, text.ifpart + "/sp // then /keyword /sp" + removeclose.text.thenpart),
     push(
      push(pop(stk1, 2), tmp)
      , prettyR(
       {prec}10
       , 7
       , if isempty.text.undertop(stk1, 2) then "// if /keyword /sp" else "// else /keyword if /sp"
      )
     )
    else if kind = kendblock ∧ n.toseq.stk ≥ 2 then
     let stk1 = reduce(stk, change)
     let noblock = width.top.stk1 < 10000
     {If clause spans multiple lines, then add a space to create space between 'else' and parens}
     let op = if noblock then "// else /keyword /sp" else "// else /keyword",
     push(
      if noblock then stk1 else push(pop.stk1, prettyR.addblock.top.stk1)
      , prettyR({prec}10, 7, op)
     )
    else if kind = kint then push(stk, prettyR.[name.sym])
    else if kind = kwords then push(stk, prettyR."//:(dq.escapeformat.worddata.sym)/literal")
    else if name.sym ∈ "$assert" then
     let reportpart = reduce(stk, change)
     let assertpart = reduce(pop.reportpart, change),
     if width.top.reportpart + 14 > maxwidth then
      push(
       pop.assertpart
       , prettyR(
        0
        , 10000
        , "// assert /keyword:(addblock.top.assertpart)/sp // report /keyword:(addblock.top.reportpart)"
       )
      )
     else
      push(
       pop.assertpart
       , prettyR."// assert /keyword:(text.top.assertpart)/sp // report /keyword:(text.top.reportpart)"
      )
    else if nopara.sym = 0 then
     let tmp =
      if kind.sym ∈ [kother, kcompoundname] then href(sym, links) else compoundName.sym,
     push(stk, prettyR.tmp)
    else if nopara.sym = 1 ∧ name.sym ∈ "(" then
     if changein then stk
     else
      let stk1 = reduce(stk, 0),
      push(pop.stk1, prettyR(0, width.top.stk1 + 2, "(:(text.top.stk1))"))
    else if nopara.sym = 1 ∧ name.sym ∈ "{" then
     {comment in header}
     {assert false report"comment1"+showZ.text.top.stk}
     push(pop.stk, prettyR."//{:(subseq(text.top.stk, 3, n.text.top.stk - 2))}/comment")
    else if nopara.sym = 1 ∧ name.sym ∈ "-" then
     {unary minus}
     let stk1 = reduce(stk, if prec.top.stk > 2 then {add()}change + 1 else change),
     push(push(push(pop.stk1, prettyR.""), top.stk1), prettyR({prec}2, 1, "-"))
    else if name.sym ∈ "%"
    ∧ nopara.sym = 1
    ∧ catStringOp = nextsym
    ∧ isString.top.pop.reduce(stk, change) then
     {handle"...:(%.exp)..."}
     let stk1 = reduce(stk, change)
     let txt = text.top.stk1,
     push(pop.stk1, prettyR."//:(dq(":" + "(:(txt))"))/literal")
    else if nopara.sym = 1 ∧ prec.top.stk < 3 ∧ kind.sym ≠ ksequence ∧ hassimplename.sym then
     {name.arg format}
     let stk1 = reduce(stk, change),
     push(push(push(pop.stk1, prettyR.href(sym, links)), top.stk1), prettyR({prec}2, 0, "."))
    else if name.sym ∈ "{" ∧ nopara.sym = 2 then
     {comment on expression}
     let expstk = reduce(stk, change)
     let comment = text.top.pop.expstk
     let comment1 = "{:(subseq(comment, 3, n.comment - 2))}",
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
       else prettyR(opprec, width.[name.sym] + 2, "/sp:(href(sym, links))/sp")
      let stk1 =
       if prec.top.stk ≠ 0 then
        let tmp = if prec.top.stk = 2 ∧ opprec = 1 then false else prec.top.stk ≥ opprec,
        reduce(stk, if tmp ∧ change > 0 then {add()}change + 1 else change)
       else stk,
      let t = pop.stk1,
      if sym = catStringOp ∧ isString.top.t then
       {handle adding back in...:()... in strings}
       let new2 =
        if isString.top.stk1 then
         let ttext = text.top.t,
         if ttext sub (n.ttext - 3) ∈ ":" ∧ (text.top.stk1) sub 6 ∈ "(" then push(stk1, prettyR(opprec."+" sub 1, 1, "/sp+/sp"))
         else push(pop.t, prettyR(text.top.t >> 2 + text.top.stk1 << 2))
        else
         push(
          pop.t
          , prettyR(text.top.t >> 2 + ":" + "(:(removeclose.text.top.stk1)):(dq)/literal")
         ),
       new2
      else if prec.top.t ∈ [0, opprec] then push(stk1, new)
      else
       let tmp = if opprec = 2 ∧ prec.top.t = 1 then false else prec.top.t > opprec,
       push(
        push(reduce(t, if tmp ∧ change > 0 then {add()}change + 1 else change), top.stk1)
        , new
       )
     else
      {create arg list}
      for stk1 = stk, args = empty:seq.prettyR, e ∈ constantseq(nopara.sym, 1)
      do
       let stkt = reduce(stk1, change),
       next(pop.stkt, [top.stkt] + args),
      if name.sym ∈ "$fortext" then
       let whileexp0 = text.args sub (n.args - 2)
       let whileexp = if whileexp0 = "true" then "" else "// while /keyword /sp:(whileexp0)"
       let accNames =
        {remove quotes}subseq(text.args sub n.args, 4, n.text.args sub n.args - 3)
       for acc6 = empty:stack.prettyR, i = 1, name ∈ accNames
       do
        if i = n.accNames ∧ name ∈ "." then {for has no sequence}next(acc6, i + 1)
        else
         let tmp =
          prettyR(%.name + (if i = n.accNames then "∈ /sp" else "= /sp") + text.args sub i),
         next(
          if i = 1 then push(acc6, tmp)
          else push(push(acc6, tmp), prettyR({prec}15, 2, ","))
          , i + 1
         )
       let accums = "// for /keyword:(removeclose.addblock.top.reduce(acc6, change))"
       let doexp0 = addblock.args sub (n.args - 1)
       let totwidth = width.doexp0 + width.whileexp + width.accums
       let doexp =
        if totwidth > maxwidth then "// do /keyword:(doexp0)"
        else "// do /keyword /sp:(doexp0)",
       let forexp =
        if totwidth > maxwidth then prettyR(0, 10000, addbr(if isempty.whileexp then accums else addbr.accums + whileexp) + doexp)
        else prettyR(accums + whileexp + "/sp" + doexp),
       push(stk1, forexp)
      else
       let w = width."():(compoundName.sym)"
       let op = prettyR({prec}15, 2, ", /sp")
       for acc = push(empty:stack.prettyR, args sub 1), p ∈ args << 1 do push(push(acc, p), op)
       let plist = top.reduce(acc, change),
       {???? adding block is not needed when one parameter and is already a block}
       if kind.sym = ksequence then push(stk1, prettyR(0, width.plist + 2, "[:(addblock.plist)]"))
       else push(stk1, prettyR(0, w + width.plist, href(sym, links) + "(" + addblock.plist + ")")),
   next(newstk, nextsym, newskip)
 let tmp = top.reduce(stk, change),
 let tmp2 = removeclose.text.tmp,
 prettyR(0, width.tmp, tmp2)

function addbr(s:seq.word) seq.word
s + if not.isempty.s ∧ blockIsLast.s then "" else "/br"

function addblock(s:prettyR) seq.word
if width.s < 10000 then text.s else "//:(text.s)/block"

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
  if prec.op = {prec}11 ∧ i = n.ops then
   next(
    addcomma(if change then removeclose.text else text) + text.op + text.e
    , addcomma(if change then removeclose.big else big) + addbr + text.op + text.e
    , width2 + width.e + width.op
    , i + 1
   )
  else if prec.op = 1 ∧ i < n.ops ∧ change then
   next(
    "(:(text):(text.op):(text.e))"
    , if isempty.big then text.op + text.e else "(:(big)/br:(text.op):(text.e))"
    , width2 + width.e + width.op
    , i + 1
   )
  else
   let op2 =
    if prec.op = 10 ∧ text.op = "// else /keyword /sp" then "/sp:(text.op)" else text.op,
   next(
    text + op2 + text.e
    , (if isempty.big then big else big + addbr) + text.op + text.e
    , width2 + width.e + width.op
    , i + 1
   )
 let finaltext = if width2 < maxwidth then text else big
 let finalwidth = if width2 < maxwidth then width2 else 10000
 let top = top.stk
 let add = addparenthesis
 {∨ prec.top ={prec}10 ∧ text.top ="// else /keyword /sp"}
 {???? Uncomment the above code to prevent parens from being dropped in \br(if a then b else c)+d being dropped /br
 adds too many parentheses. }
 let new =
  if change ∧ add ∧ prec.top ≠ {prec}11 then prettyR(0, width2 + 2, "(:(finaltext))")
  else prettyR(0, finalwidth, finaltext),
 push(pop.acc1, new)

function width(s:seq.prettyR) int
for width = 0, e ∈ s do width + width.e,
width

function catStringOp symbol
symbol(moduleref("* seq", typeword), "+", [seqof.typeword, seqof.typeword], seqof.typeword)

function isString(b:prettyR) boolean
text.b << (n.text.b - 2) = dq + "/literal" ∧ subseq(text.b, 1, 2) = "//:(dq)"

Function id(sym:symbol) seq.word
for txt = "", type ∈ types.sym do txt + ":" + %.type,
if issimplename.sym then [name.sym] + txt else [name.sym] + ":" + txt

function print(s:set.autolink) seq.word
for acc = "", e ∈ toseq.s do acc + id.e + "file" + file.e + "/br",
acc

function href(sym:symbol, links:set.autolink) seq.word
if isempty.links then compoundName.sym
else
 let symid = id.sym
 let links2 = find(links, symid),
 if isempty.links2 then compoundName.sym
 else
  let match =
   if n.links2 = 1 then links2 sub 1
   else
    for match = autolink("", ""), e ∈ toseq.links2
    while firstT.match = 0
    do
     if symid = id.e then e
     else if firstT.e < n.id.e ∧ firstT.e < n.symid then
      {for when id.e has a T. The T must be replaced with the actual type}
      let T =
       subseq(symid, firstT.e, firstT.e + findindex(symid << firstT.e, ":" sub 1) - 1)
      for neweid = "", w ∈ id.e do if w ∈ "T" then neweid + T else neweid + w,
      if neweid = symid then e else match
     else match,
    match
  let result =
   let tmp = if isempty.file.match then "" else "/tag:(file.match)",
   "// //:(tmp)/nsp # /nsp:(id.match)/href:(compoundName.sym)/a",
  assert name.sym ∉ "subseq" ∨ n.links2 = 1 report "xx:(print.asset.[match])" + result + "/p" + print.find(links, symid),
  result

Function pretty(
header:seq.word
, code:seq.symbol
, syms:set.autolink
, change:boolean
) seq.word
let body = pretty(code, syms, change)
let h = if width.header < maxwidth then header else formatHeader.header,
if width.header + width.body < maxwidth then h + "/sp" + text.body
else h + "/br" + text.body

Function escapeformat(in:seq.word) seq.word
if width.in < maxwidth then [escapeformat] + in + escapeformat
else
 for result = [escapeformat], w ∈ in
 do
  if w
  ∈ "/br /p
  /tr
  "
  ∧ n.result > 1 then result + w + escapeformat + "/br" + escapeformat
  else result + w,
 result + escapeformat

Function compoundNameType mytype typeref."internal internal:"

function hassimplename(s:symbol) boolean
if resulttype.s = compoundNameType then false else issimplename.s

function compoundName(s:symbol) seq.word
if resulttype.s = compoundNameType then towords(emptyUTF8 + decodeword.name.s)
else fullname.s 

