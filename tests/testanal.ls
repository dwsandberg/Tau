Module testanal

use standard

use symbol

use otherseq.symbol

use newanal

use seq.mytype

Function analtests seq.word
let typegraph = addabstract(typeref."graph graph *", typeword)
let inputs = [
 analtest(
  symbol(internalmod, "recursiveWpart", typegraph, seqof.typeword, seqof.typeword, seqof.typeword)
  , "%1 %2 sinks (graph.word, seq.word) seq.word Define 4 Start (seq.int) %4 getseqlength (
  ptr) int 0 = (int, int) boolean Br2 (1, 2) %3 Exit %1 %2 %4 seq.word:asset (seq.word
  ) seq.word seq.word:+(seq.word, seq.word) seq.word %3 %4 seq.word:+(seq.
  word, seq.word) seq.word recursiveWpart (graph.word, seq.word, seq.word) seq.word
  Exit EndBlock"
  , "%1 %2 %3 Loop:4 (graph.word, seq.word, seq.word) seq.word
  /br %4 %5 sinks (graph.word, seq.word) seq.word Define 7 %7 getseqlength (ptr) int 0 = (
  int, int) boolean Br2 (1, 2)
  /br %6 Exit
  /br %4 %5 %7 seq.word:asset (seq.word) seq.word seq.word:+(seq.word, seq.word
  ) seq.word %6 %7 seq.word:+(seq.word, seq.word) seq.word Continue 3
  /br EndBlock
  /br"
 )
 , analtest(
  symbol(internalmod, "basic", typeint, typeint, typeint)
  , "Start (int) %1 3 = (int, int) boolean Br2 (1, 2) %1 Exit %2 Exit EndBlock"
  , "Start (int)
  /br %1 3 = (int, int) boolean Br2 (1, 2)
  /br %1 Exit
  /br %2 Exit
  /br EndBlock
  /br"
 )
 , analtest(
  Lit.11
  , "Start (int) %1 4 > (int, int) boolean Br2 (1, 2) Start (int) %1 5 = (int, int) boolean
  Br2 (1, 2) 6 Exit 7 Exit EndBlock Exit %1 5 = (int, int) boolean Br2 (1, 2) 6 Exit 7 Exit
  EndBlock"
  , "Start (int)
  /br %1 4 > (int, int) boolean Br2 (1, 1)
  /br %1 5 = (int, int) boolean Br2 (1, 2)
  /br 6 Exit
  /br 7 Exit
  /br EndBlock
  /br"
 )
 , analtest(
  Lit.22
  , "1 Define 2 Start (int) %1 1 = (int, int) boolean Br2 (1, 2) 1 Exit 2 Define 3 Start (int)
  %1 2 = (int, int) boolean Br2 (1, 2) 2 Exit 3 Define 4 Start (int) %1 3 = (int, int)
  boolean Br2 (1, 2) %2 %3+(int, int) int %4+(int, int) int Exit 3 Exit EndBlock Exit
  EndBlock Exit EndBlock"
  , "1 Define 2 Start (int)
  /br %1 1 = (int, int) boolean Br2 (1, 2)
  /br 1 Exit
  /br 2 Define 3 %1 2 = (int, int) boolean Br2 (1, 2)
  /br 2 Exit
  /br 3 Define 4 %1 3 = (int, int) boolean Br2 (1, 2)
  /br %2 %3+(int, int) int %4+(int, int) int Exit
  /br 3 Exit
  /br EndBlock
  /br"
 )
 , analtest(
  Lit.33
  , "1 Define 2 Start (int) false boolean Br2 (1, 2) 1 Exit 2 Define 3 Start (int) false boolean
  Br2 (1, 2) 2 Exit 3 Define 4 Start (int) true boolean Br2 (1, 2) %2 %3+(int, int) int
  %4+(int, int) int Exit 3 Exit EndBlock Exit EndBlock Exit EndBlock"
  , "1 Define 2 2 Define 3 3 Define 4 %2 %3+(int, int) int %4+(int, int) int"
 )
 , analtest(
  Words."loopisnoop"
  , "seq.int:empty:seq.int seq.int %1 Define 2 %2 getseqlength (ptr) int Define 3 0 Loop:4
  (seq.int, int) int %5 %3 = (int, int) boolean Br2 (1, 2) 0 Exit %5 1+(int, int) int
  Define 6 %2 %6 idxNB (seq.char, int) int Define 7 %4 %7 seq (1) seq.int seq.int:+(
  seq.int, seq.int) seq.int %6 Continue 2 EndBlock Define 8 %4"
  , "seq.int:empty:seq.int seq.int %1 Define 2 %2 seq.int:+(seq.int, seq.int) seq
  .int Define 4 0 Define 8 %4"
 )
 , analtest(
  symbol(internalmod, "recursive", typeint, typeint, typeint)
  , "Start (int) %1 1 = (int, int) boolean Br2 (1, 2) %2 Exit %1 1-(int, int) int %1 %2 * (
  int, int) int recursive (int, int) int Exit EndBlock"
  , "%1 %2 Loop:3 (int, int) int
  /br %3 1 = (int, int) boolean Br2 (1, 2)
  /br %4 Exit
  /br %3 1-(int, int) int %3 %4 * (int, int) int Continue 2
  /br EndBlock
  /br"
 )
 , analtest(
  Words."boolean block"
  , "Start (int) %1 9 = (int, int) boolean Br2 (1, 4) Start (boolean) %1 3 = (int, int)
  boolean Br2 (1, 2) 5 Define 2 3 3 = (int, int) boolean Exit false boolean Exit EndBlock Br2 (
  1, 2) 1 1+(int, int) int Exit %1 5 * (int, int) int 4+(int, int) int Exit 9 Exit
  EndBlock"
  , "Start (int)
  /br %1 9 = (int, int) boolean Br2 (1, 5)
  /br %1 3 = (int, int) boolean Br2 (1, 3)
  /br 5 Define 2 3 3 = (int, int) boolean Br2 (1, 2)
  /br 1 1+(int, int) int Exit
  /br %1 5 * (int, int) int 4+(int, int) int Exit
  /br 9 Exit
  /br EndBlock
  /br"
 )
 , analtest(
  Words."tricky case"
  , "Start (int) %1 2 = (int, int) boolean Br2 (3, 1) %1 4 = (int, int) boolean Br2 (2, 1)
  %1 3 = (int, int) boolean Br2 (2, 3) true boolean Br2 (1, 1) true boolean Br2 (2, 2) %2
  0 > (int, int) boolean Br2 (1, 2) 2 Exit 3 Exit EndBlock"
  , "Start (int)
  /br %1 2 Jump (int, int) boolean Br2 (4, 1)
  /br 4 Br2 (3, 1)
  /br 3 Br2 (2, 1)
  /br %2 0 > (int, int) boolean Br2 (1, 2)
  /br 2 Exit
  /br 3 Exit
  /br EndBlock
  /br"
 )
 , analtest(
  Words."simple run"
  , "Start (int) %1 5 = (int, int) boolean Br2 (1, 2) 6 Exit %1 3 = (int, int) boolean Br2 (
  1, 2) 4 Exit %1 1 = (int, int) boolean Br2 (1, 2) 2 Exit 8 Exit EndBlock"
  , "Start (int)
  /br %1 5 Jump (int, int) boolean Br2 (3, 1)
  /br 3 Br2 (3, 1)
  /br 1 Br2 (3, 4)
  /br 6 Exit
  /br 4 Exit
  /br 2 Exit
  /br 8 Exit
  /br EndBlock
  /br"
 )
 , analtest(
  Words."run 2"
  , "Start (int) %3 5 = (int, int) boolean Br2 (4, 1) %3 2 = (int, int) boolean Br2 (3, 1)
  %3 12 = (int, int) boolean Br2 (2, 1) %3 3 = (int, int) boolean Br2 (2, 3) 10 Exit 10
  Exit 11 Exit EndBlock"
  , "Start (int)
  /br %3 5 Jump (int, int) boolean Br2 (4, 1)
  /br 2 Br2 (3, 1)
  /br 12 Br2 (2, 1)
  /br 3 Br2 (1, 2)
  /br 10 Exit
  /br 11 Exit
  /br EndBlock
  /br"
 )
 , analtest(
  Words."run 4"
  , "1 2 3 Loop:5 (int, int, int) int %12 %7 = (int, int) boolean Br2 (1, 2) 0 Exit %14 2 =
  (int, int) boolean Br2 (2, 1) %14 4 = (int, int) boolean Br2 (2, 3) true boolean Br2 (
  1, 2) %5 %6 %5 Continue 3 %14 3 = (int, int) boolean Br2 (1, 2) %5 %6 %4 Continue 3 %2 4 =
  (int, int) boolean Br2 (2, 1) %2 5 = (int, int) boolean Br2 (2, 3) true boolean Br2 (1
  , 2) %5 %6 %8 Continue 3 %5 %6 %9 Continue 3 EndBlock"
  , "1 2 3 Loop:5 (int, int, int) int
  /br %12 %7 = (int, int) boolean Br2 (1, 2)
  /br 0 Exit
  /br %14 2 Jump (int, int) boolean Br2 (3, 1)
  /br 4 Br2 (2, 1)
  /br 3 Br2 (2, 3)
  /br %5 %6 %5 Continue 3
  /br %5 %6 %4 Continue 3
  /br %2 4 = (int, int) boolean Br2 (2, 1)
  /br %2 5 = (int, int) boolean Br2 (1, 2)
  /br %5 %6 %8 Continue 3
  /br %5 %6 %9 Continue 3
  /br EndBlock
  /br"
 )
 , analtest(
  Words."jump"
  , "Start (int) %1 1 Jump (int, int) boolean Br2 (5, 1) 2 Br2 (5, 1) 5 Br2 (5, 1) 7 Br2 (
  5, 1) 0 Exit 1 Exit 2 Exit 5 Exit 7 Exit EndBlock"
  , "Start (int)
  /br %1 1 Jump (int, int) boolean Br2 (5, 1)
  /br 2 Br2 (5, 1)
  /br 5 Br2 (5, 1)
  /br 7 Br2 (5, 1)
  /br 0 Exit
  /br 1 Exit
  /br 2 Exit
  /br 5 Exit
  /br 7 Exit
  /br EndBlock
  /br"
 )
 , analtest(
  Words."FDSF"
  , "Start (int) %1 8 = (int, int) boolean Br2 (1, 2) %4 Exit %1 9 = (int, int) boolean Br2 (
  1, 2) %4 Exit %1 10 = (int, int) boolean Br2 (2, 1) %1 11 = (int, int) boolean Br2 (1,
  2) %4 Exit %1 12 = (int, int) boolean Br2 (2, 1) %1 13 = (int, int) boolean Br2 (1, 2)
  %4 Exit %1 14 = (int, int) boolean Br2 (1, 2) 14 Exit 9 Exit EndBlock"
  , "Start (int)
  /br %1 8 Jump (int, int) boolean Br2 (7, 1)
  /br 9 Br2 (6, 1)
  /br 10 Br2 (5, 1)
  /br 11 Br2 (4, 1)
  /br 12 Br2 (3, 1)
  /br 13 Br2 (2, 1)
  /br 14 Br2 (2, 3)
  /br %4 Exit
  /br 14 Exit
  /br 9 Exit
  /br EndBlock
  /br"
 )
]
for acc = "", test ∈ inputs
do
 let a = %.newanal(tosymbols(in.test, self.test), self.test),
  acc
   + 
   if a ≠ out.test then
   "Fail^(self.test) Input:^(tosymbols(in.test, self.test)) Expected:^(out.test) got:^(a)"
   else "Pass^(self.test)",
acc

type analtest is self:symbol, in:seq.word, out:seq.word

use seq.analtest

function tosymbols(in:seq.word, self:symbol) seq.symbol
let typegraph = addabstract(typeref."graph graph *", typeword)
for X = "Exit EndBlock", XR = [Exit, EndBlock], i ∈ arithseq(15, 1, 0)
do next(X + merge."%^(i)" + %.i, XR + Local.i + Lit.i)
let X2R =
 [
  Br2(1, 2)
  , Br2(1, 4)
  , Br2(2, 1)
  , Br2(2, 2)
  , Br2(2, 3)
  , Br2(1, 1)
  , Br2(3, 1)
  , Br2(4, 1)
  , Br2(5, 1)
  , Br2(6, 1)
  , EqOp
  , JumpOp
  , GtOp
  , Start.typeint
  , Start.typeboolean
  , PlusOp
  , Littrue
  , Litfalse
  , symbol(moduleref("* seq", typeint), "+", seqof.typeint, seqof.typeint, seqof.typeint)
  , Sequence(typeint, 1)
  , symbol(internalmod, "idxNB", seqof.typechar, typeint, typeint)
  , Loopblock([seqof.typeint, typeint], 4, typeint)
  , Loopblock([typeint, typeint, typeint], 5, typeint)
  , GetSeqLength
  , symbol(internalmod, "*", typeint, typeint, typeint)
  , symbol(internalmod, "-", typeint, typeint, typeint)
 ]
  + self
  + [
  symbol(internalmod, "sinks", typegraph, seqof.typeword, seqof.typeword)
  , symbol(moduleref("* seq", typeword), "+", seqof.typeword, seqof.typeword, seqof.typeword)
  , symbol(moduleref("* seq", typeword), "asset", seqof.typeword, seqof.typeword)
  , Start.seqof.typeint
 ]
for X3 = empty:seq.seq.word, e ∈ X2R
do
 let h = %.e
 let hh0 = if 1^h ∈ "/br" then h >> 1 else h
 let j = findindex(hh0, 1#":"),
 X3 + if j > n.hh0 then hh0 else hh0 << j
let inarg = 2
for acc = empty:seq.symbol, arg = "", typ = "", state = 0, w ∈ reverse.in
do
 if w ∈ ")" then
 next(acc, "", typ, inarg)
 else if w ∈ "(" then
 next(acc, arg, typ, 0)
 else if state = inarg then
 next(acc, [w] + arg, typ, inarg)
 else if w ∈ "empty" then
 next(
  [symbol4(moduleref("* seq", typeint), 1#"empty", seqof.typeint, empty:seq.mytype, seqof.typeint)]
   + acc
  , arg
  , typ
  , 0
 )
 else if w ∈ ":Loop: " then
 next(acc, arg, "", 0)
 else if isempty.arg ∧ w ∈ "int boolean.seq word graph" then
 next(acc, arg, [w] + typ, 0)
 else if w ∈ "Define" then
 next([Define.value.1#acc] + acc << 1, arg, typ, 0)
 else if w ∈ "Continue" then
 next([continue.value.1#acc] + acc << 1, arg, typ, 0)
 else
  let j = findindex(X, w),
   if isempty.arg ∧ j ≤ n.X then
   next([j#XR] + acc, arg, "", 0)
   else
    assert not(isempty.arg ∧ isempty.typ)
    report "Confusion with Word" + w + "/p" + %.acc
    let t2 = if isempty.arg then %.w + typ else %.w + "(" + arg + ")" + typ
    for i = 1, e ∈ X3 while subseq(t2, 1, n.e) ≠ e do i + 1
    assert i ≤ n.X3 report "SDF^(w) (^(arg))^(typ)^(in)",
    next([i#X2R] + acc, "", "", 0)
for xx = "", w ∈ %.acc do if w ∈ "/br" then xx else xx + w
assert xx = in report "DIFF^(in) /p^(xx)",
acc

use otherseq.word

use otherseq.seq.word 