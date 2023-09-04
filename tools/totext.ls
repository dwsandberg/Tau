Module totext

use UTF8

use backparse

use format

use otherseq.int

use seq.int

use seq.seq.int

use otherseq.mytype

use seq.mytype

use newPretty

use otherseq.paravalues

use standard

use symbol

use otherseq.symbol

use otherseq.word

use seq.word

use otherseq.seq.word

use seq.seq.word

use stack.seq.word

type paravalues is parano:int, value:seq.symbol

function >1(a:paravalues, b:paravalues) ordering parano.a >1 parano.b

function %(p:paravalues) seq.word "::^(parano.p)^(value.p)"

Function replace(
 code:seq.symbol
 , pattern:seq.symbol
 , replacement:seq.symbol
 , nopara:int
) seq.symbol
let tmp = replace2(code, pattern, replacement, nopara),
if isempty.tmp then code else tmp

function eq2(p:mytype, a:mytype) boolean
abstracttypename.p = 1_"*"
 ∨ p = a
 ∨ abstracttype.p = abstracttype.a ∧ eq2(parameter.p, parameter.a)

function sametypes(p:symbol, a:symbol) boolean
let tomatch = types.p
for same = true, idx = 1, atype ∈ types.a
while same
do let ptype = idx_tomatch, next(eq2(ptype, atype), idx + 1)
assert true report "^(tomatch)^(types.a)^(if same then "same" else "")",
same

Function replace2(
 code:seq.symbol
 , pattern:seq.symbol
 , replacement:seq.symbol
 , nopara:int
) seq.symbol
if n.code < n.pattern then
empty:seq.symbol
else
 for A = empty:seq.int, skip = 0, patternidx = n.pattern, place = n.code, sym ∈ reverse.code
 while patternidx > 0
 do
  if skip > 0 then
  next(A, skip - 1, patternidx, place - 1)
  else
   let p = patternidx_pattern,
    if islocal.p ∧ value.p ≤ nopara then
     let z = backparse3(code, place, nopara - n.A = 1),
     next(A + [value.p, z, place], place - z, patternidx - 1, place - 1)
    else if
     name.module.p = name.module.sym
     ∧ name.p = name.sym
     ∧ nopara.p = nopara.sym
     ∧ sametypes(p, sym)
    then
    next(if patternidx = n.pattern then [place] else A, skip, patternidx - 1, place - 1)
    else next(empty:seq.int, 0, n.pattern, place - 1),
  if isempty.A ∨ patternidx ≠ 0 then
  empty:seq.symbol
  else
   for acc = empty:seq.paravalues, i ∈ arithseq(n.A / 3, 3, 2)
   do setinsert(
    acc
    , paravalues(i_A, replace(subseq(code, (i + 1)_A, (i + 2)_A), pattern, replacement, nopara))
   )
   {assert false report" GG"+%n.acc}
   for new = empty:seq.symbol, sym ∈ replacement
   do if islocal.sym then new + value.(value.sym)_acc else new + sym,
    replace(code >> (n.code - place + skip), pattern, replacement, nopara)
    + new
    + code << 1_A

Function totext(src:seq.seq.word, sd:symdef) seq.word
let src2 = (paragraphno.sd)_src
let newheader =
 if nopara.sym.sd = 0 then
 fullname.sym.sd
 else fullname.sym.sd + subseq(src2, findindex(src2, 1_"("), findindex(src2, 1_")"))
let c = code.sd
let newtext =
 [1_src2]
 + newheader
 + %.resulttype.sym.sd
 + 
  for stk = empty:stack.seq.word, last = 1_c, sym ∈ c << 1
  do
   if sym = NotOp ∧ nopara.last = 2 then
    let paratypes = paratypes.last
    let newname =
     if name.last = 1_"=" then
     "≠"
     else if name.last = 1_"∈" then
     "∉"
     else if name.last = 1_"<" then
     "≥"
     else if name.last = 1_">" then
     "≤"
     else [name.last],
     if name.last ≠ 1_newname then
     next(stk, symbol(internalmod, newname, 1_paratypes, 2_paratypes, typeboolean))
     else next(newstk(last, stk), sym)
   else if
    sym
    = symbol(moduleref("* seq", typeword), "+", [seqof.typeword, seqof.typeword], seqof.typeword)
    ∧ name.last ∈ "%"
    ∧ nopara.last = 1
    ∧ resulttype.last = resulttype.sym
    ∧ n.toseq.stk > 1
    ∧ isString.top.pop.stk
   then
   next(stk, sym)
   else next(newstk(last, stk), sym),
  top.newstk(last, stk)
{pretty twice to clean up expressions (a+(b+d))}
pretty.towords.textformat.pretty.newtext

Function showZ(out:seq.word) seq.word
for acc = "", w ∈ out do acc + encodeword(decodeword.w + char1."Z"),
acc

function newstk(sym:symbol, stk:stack.seq.word) stack.seq.word
if isstart.sym then
push(stk, "if")
else if isbr.sym then
let args = top(stk, 2), push(pop(stk, 2), 1_args + 2_args + "then")
else if isExit.sym then
let args = top(stk, 2), push(pop(stk, 2), 1_args + 2_args + "else if")
else if isblock.sym ∧ n.toseq.stk ≥ 2 then
let args = top(stk, 2), push(pop(stk, 2), "(^(1_args >> 1 + 2_args))")
else if name.module.sym ∈ "$int" then
push(stk, [name.sym])
else if iswords.sym then
push(stk, dq + worddata.sym + dq)
else if name.sym = 1_"let" ∧ n.toseq.stk ≥ 2 then
let args = top(stk, 2), push(pop(stk, 2), 1_args + "(" + 2_args + ")")
else if isdefine.sym ∧ not.isempty.stk then
push(pop.stk, "let^([name.sym]) = (^(top.stk))")
else if name.sym ∈ "{" ∧ n.toseq.stk ≥ 1 then
 {comment}
 if nopara.sym = 1 then
 push(pop.stk, "{^(subseq(top.stk, 2, n.top.stk - 1))}")
 else
  let args = top(stk, 2),
  push(pop(stk, 2), "{^(subseq(1_args, 2, n.1_args - 1))}^(2_args)")
else if name.sym ∈ "assert" then
stk
else if name.sym ∈ "makereal" ∧ 3_top.stk = 1_"." then
push(pop.stk, subseq(top.stk, 2, n.top.stk - 1))
else if name.sym = 1_"report" ∧ n.toseq.stk ≥ 3 then
 let args = top(stk, 3),
 push(pop(stk, 3), "assert^(1_args) report (^(3_args)) (^(2_args))")
else if
 sym
 = symbol(moduleref("* seq", typeword), "+", [seqof.typeword, seqof.typeword], seqof.typeword)
 ∧ isString.top.pop.stk
then
 let args = top(stk, 2)
 let result =
  if 1_2_args ∉ dq then
  1_args >> 1 + "^" + "(^(2_args))^(dq)"
  else if
   2^1_args ∈ "^" ∧ 2_2_args ∈ "("
   ∨ 1_args << (n.1_args - 2) = "^" + "("
   ∨ not.oktocombine(1_args, 2_args)
  then
  "^(1_args)+^(2_args)"
  else 1_args >> 1 + 2_args << 1,
 push(pop(stk, 2), result)
else if nopara.sym = 2 ∧ name.sym ∈ binaryops ∧ n.toseq.stk ≥ 2 then
 let args = top(stk, 2)
 let arg1 = if name.sym ∈ "_^" then "(^(1_args))" else 1_args,
 push(pop(stk, 2), "(^(arg1)^(name.sym)^(2_args))")
else if nopara.sym = 2 ∧ name.sym ∈ "^" then
 let args = top(stk, 2)
 let new =
  if 1_2_args ∈ dq ∧ 1_1_args ∈ dq then
  1_args >> 1 + 2_args << 1
  else 1_args >> 1 + "^" + "(" + 2_args + ")" + dq,
 push(pop(stk, 2), new)
else if name.sym ∈ "$mergecode" then
let args = top(stk, 2), push(pop(stk, 2), 1_args + 2_args)
else if name.sym ∈ "$assert" then
let args = top(stk, 2), push(pop(stk, 2), "assert^(1_args) report^(2_args)")
else if name.sym ∈ "$letend" then
 let args = top(stk, nopara.sym)
 for acc7 = "", s ∈ args >> 1 do acc7 + s,
 push(pop(stk, nopara.sym), acc7 + "," + 1^args)
else if name.sym ∈ "$fortext" then
 let args = top(stk, nopara.sym)
 let whileexp = 3^args
 let accNames = {remove quotes} subseq(1^args, 2, n.1^args - 1)
 for acc6 = "for", i = 1, name ∈ accNames
 do
  let tmp =
   if i = n.accNames then
   if name ∈ "." then "" else "^(name) ∈^(i_args),"
   else "^(name) =^(i_args),",
  next(acc6 + tmp, i + 1)
 let forexp =
  acc6 >> 1
  + (if whileexp = "true" then "" else "while^(whileexp)")
  + "do^((n.args - 1)_args),",
 push(pop(stk, nopara.sym), forexp)
else if n.toseq.stk ≥ nopara.sym then
 for plist = "", t ∈ top(stk, nopara.sym) do plist + t + ",",
 push(
  pop(stk, nopara.sym)
  , if isSequence.sym then
   "[^(plist >> 1)]"
   else if nopara.sym = 0 then
   fullname.sym
   else fullname.sym + "(^(plist >> 1))"
 )
else stk

function oktocombine(a:seq.word, b:seq.word) boolean
{???? remove}
for w1 = 0, last = 1_"?", e ∈ reverse.a
while not(e ∈ "/br /p" ∨ e ∈ "+" ∧ last ∈ dq)
do next(w1 + wordwidth.e, e)
for w2 = 0, e ∈ b while e ∉ "/br /p" do w2 + wordwidth.e,
w1 + w2 < 10000

function wordwidth(w:word) int
if w ∈ ("<* *> /keyword: ./nosp" + escapeformat) then
0
else if w ∈ "(,) /ldq /sp" then
1
else n.decodeword.w + 1

function isString(b:seq.word) boolean let b1 = subseq(b, n.b - 1, n.b), 1^b1 ∈ dq

function binaryops seq.word "=+_^∩ ∪ \-* / << >> > < ? >1 >2 ∈ mod ∧ ∨ ⊻ ≠ ∉ ≥ ≤"

Export backparse3(s:seq.symbol, i:int, includeDefine:boolean) int 