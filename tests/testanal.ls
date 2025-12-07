Module testanal.T

use standard

use symbol1

use seq1.symbol

use compilerfrontT.T

use seq.mytype

Function analtests:T seq.word
let typegraph = addabstract(typeref."graph graph *", typeword)
let inputs =
 [
  analtest(
   symbol(internalmod, "recursiveWpart", [typegraph, seqof.typeword, seqof.typeword], seqof.typeword)
   , "%1 %2 sinks(graph.word, seq.word)seq.word Define 4 Start(seq.int)%4 getseqlength(ptr)int 0 =(int, int)boolean Br2(1, 2)%3 Exit %1 %2 %4 seq.word:asset(seq.word)seq.word seq.word:+(seq.word, seq.word)seq.word %3 %4 seq.word:+(seq.word, seq.word)seq.word recursiveWpart(graph.word, seq.word, seq.word)seq.word Exit EndBlock"
   , "%1 %2 %3 Loop:4(graph.word, seq.word, seq.word)seq.word /br
   %4 %5 sinks(graph.word, seq.word)seq.word Define 7 %7 getseqlength(ptr)int 0 =(int, int)boolean Br2(1, 2)/br
   %6 Exit /br
   %4 %5 %7 seq.word:asset(seq.word)seq.word seq.word:+(seq.word, seq.word)seq.word %6 %7 seq.word:+(seq.word, seq.word)seq.word Continue 3 /br
   EndBlock /br
   "
  )
  , analtest(
   symbol(internalmod, "basic", [typeint, typeint], typeint)
   , "Start(int)%1 3 =(int, int)boolean Br2(1, 2)%1 Exit %2 Exit EndBlock"
   , "Start(int)/br
   %1 3 =(int, int)boolean Br2(1, 2)/br
   %1 Exit /br
   %2 Exit /br
   EndBlock /br
   "
  )
  , analtest(
   symbol(internalmod, "basic11", [typeint], typeint)
   , "Start(int)%1 4 >(int, int)boolean Br2(1, 2)Start(int)%1 7777 =(int, int)boolean Br2(1, 2)6 Exit 7 Exit EndBlock Exit %1 7777 =(int, int)boolean Br2(1, 2)6 Exit 7 Exit EndBlock"
   , "Start(int)/br
   %1 4 >(int, int)boolean Br2(1, 1)/br
   %1 7777 =(int, int)boolean Br2(1, 2)/br
   6 Exit /br
   7 Exit /br
   EndBlock /br
   "
  )
  , analtest(
   symbol(internalmod, "basic22", [typeint, typeint, typeint], typeint)
   , "Start(int)%1 1 =(int, int)boolean Br2(1, 2)1 Exit 2 Define 3 Start(int)2 %1 =(int, int)boolean Br2(1, 2)2 Exit 3 Define 4 Start(int)%1 3 =(int, int)boolean Br2(1, 2)%2 %3+(int, int)int %4+(int, int)int Exit 3 Exit EndBlock Exit EndBlock Exit EndBlock"
   , "Start(int)/br
   %1 1 =(int, int)boolean Br2(1, 2)/br
   1 Exit /br
   2 %1 =(int, int)boolean Br2(1, 2)/br
   2 Exit /br
   %1 3 =(int, int)boolean Br2(1, 2)/br
   %2 2+(int, int)int 3+(int, int)int Exit /br
   3 Exit /br
   EndBlock /br
   "
  )
  , analtest(
   symbol(internalmod, "basic33", [typeint, typeint, typeint], typeint)
   , "Start(int)false boolean Br2(1, 2)1 Exit Start(int)false boolean Br2(1, 2)2 Exit 3 Define 4 Start(int)true boolean Br2(1, 2)%2 %3+(int, int)int %4+(int, int)int Exit 3 Exit EndBlock Exit EndBlock Exit EndBlock"
   , "%2 %3+(int, int)int 3+(int, int)int"
  )
  , analtest(
   symbol(internalmod, "loopisnoop", [typeint, typeint], typeint)
   , "seq.int:empty:seq.int seq.int %2 getseqlength(ptr)int Define 3 0 Loop:4(seq.int, int)int %5 %3 =(int, int)boolean Br2(1, 2)0 Exit %5 1+(int, int)int Define 6 %2 %6 idxNB(seq.int, int)int Define 7 %4 %7 seq(1)seq.int seq.int:+(seq.int, seq.int)seq.int %6 Continue 2 EndBlock Define 8 %4"
   , "seq.int:empty:seq.int seq.int %2 seq.int:+(seq.int, seq.int)seq.int Define 4 %4"
  )
  , analtest(
   symbol(internalmod, "recursive", [typeint, typeint], typeint)
   , "Start(int)%1 1 =(int, int)boolean Br2(1, 2)%2 Exit %1 1-(int, int)int %1 %2 *(int, int)int recursive(int, int)int Exit EndBlock"
   , "%1 %2 Loop:3(int, int)int /br
   %3 1 =(int, int)boolean Br2(1, 2)/br
   %4 Exit /br
   %3 1-(int, int)int %3 %4 *(int, int)int Continue 2 /br
   EndBlock /br
   "
  )
  , analtest(
   symbol(internalmod, "booleanBlock", [typeint, typeint], typeint)
   , "Start(int)%1 9 =(int, int)boolean Br2(1, 4)Start(boolean)%1 3 =(int, int)boolean Br2(1, 2)3 3 =(int, int)boolean Exit false boolean Exit EndBlock Br2(1, 2)%2 1+(int, int)int Exit %1 5 *(int, int)int 4+(int, int)int Exit 9 Exit EndBlock"
   , "Start(int)/br
   %1 9 =(int, int)boolean Br2(2, 1)/br
   9 Exit /br
   %1 3 =(int, int)boolean Br2(1, 2)/br
   %2 1+(int, int)int Exit /br
   %1 5 *(int, int)int 4+(int, int)int Exit /br
   EndBlock /br
   "
  )
  , analtest(
   symbol(internalmod, "tricky_case", [typeint, typeint], typeint)
   , "Start(int)%1 2 =(int, int)boolean Br2(3, 1)%1 4 =(int, int)boolean Br2(2, 1)%1 3 =(int, int)boolean Br2(2, 3)true boolean Br2(1, 1)true boolean Br2(2, 2)%2 0 >(int, int)boolean Br2(1, 2)2 Exit 3 Exit EndBlock"
   , "Start(int)/br
   %1 JmpB 9 2:2 4:2 3:2:1 Jmp 9 /br
   %2 0 >(int, int)boolean Br2(1, 2)/br
   2 Exit /br
   3 Exit /br
   EndBlock /br
   "
  )
  , analtest(
   symbol(internalmod, "simplerun", [typeint, typeint], typeint)
   , "Start(int)%1 5 =(int, int)boolean Br2(1, 2)6 Exit %1 3 =(int, int)boolean Br2(1, 2)4 Exit %1 1 =(int, int)boolean Br2(1, 2)2 Exit 8 Exit EndBlock"
   , "Start(int)/br
   %1 JmpB 9 5:1 3:2 1:3:4 Jmp 9 /br
   6 Exit /br
   4 Exit /br
   2 Exit /br
   8 Exit /br
   EndBlock /br
   "
  )
  , analtest(
   symbol(internalmod, "run_2", [typeint, typeint, typeint], typeint)
   , "Start(int)%3 5 =(int, int)boolean Br2(4, 1)%3 2 =(int, int)boolean Br2(3, 1)%3 12 =(int, int)boolean Br2(2, 1)%3 3 =(int, int)boolean Br2(2, 3)10 Exit 10 Exit 11 Exit EndBlock"
   , "Start(int)/br
   %3 JmpB 11 5:1 2:1 12:1 3:1:2 Jmp 11 /br
   10 Exit /br
   11 Exit /br
   EndBlock /br
   "
  )
  , analtest(
   symbol(
    internalmod
    , "run4"
    , [typeint, typeint, typeint, typeint, typeint, typeint, typeint]
    , typeint
   )
   , "1 2 3 Loop:5(int, int, int)int %10 %7 =(int, int)boolean Br2(1, 2)0 Exit %1 2 =(int, int)boolean Br2(2, 1)%1 4 =(int, int)boolean Br2(2, 3)true boolean Br2(1, 2)%5 %6 %5 Continue 3 %1 3 =(int, int)boolean Br2(1, 2)%5 %6 %4 Continue 3 %2 4 =(int, int)boolean Br2(2, 1)%2 5 =(int, int)boolean Br2(2, 3)true boolean Br2(1, 2)%5 %6 %8 Continue 3 %5 %6 %9 Continue 3 EndBlock"
   , "1 2 3 Loop:8(int, int, int)int /br
   %10 %10 =(int, int)boolean Br2(1, 2)/br
   0 Exit /br
   %1 JmpB 9 2:4 4:4 3:1:2 Jmp 9 /br
   %8 %9 %4 Continue 3 /br
   %2 4 =(int, int)boolean Br2(2, 1)/br
   %2 5 =(int, int)boolean Br2(1, 2)/br
   %8 %9 %8 Continue 3 /br
   %8 %9 %9 Continue 3 /br
   EndBlock /br
   "
  )
  , analtest(
   symbol(internalmod, "jump", [typeint, typeint], typeint)
   , "Start(int)%1 JmpB 11 1:1 2:2 5:3 7:4:5 Jmp 11 1 Exit 2 Exit 5 Exit 7 Exit 0 Exit EndBlock"
   , "Start(int)/br
   %1 JmpB 11 1:1 2:2 5:3 7:4:5 Jmp 11 /br
   1 Exit /br
   2 Exit /br
   5 Exit /br
   7 Exit /br
   0 Exit /br
   EndBlock /br
   "
  )
  , analtest(
   symbol(internalmod, "jump2", [typeint, typeint], typeint)
   , "Start(int)5 JmpB 11 1:1 2:2 5:3 7:4:5 Jmp 11 1 Exit 2 Exit 5 Exit 7 Exit 0 Exit EndBlock"
   , "5"
  )
  , analtest(
   symbol(internalmod, "jump3", [typeint, typeint], typeint)
   , "Start(int)14 JmpB 11 1:1 2:2 5:3 7:4:5 Jmp 11 1 Exit 2 Exit 5 Exit 7 Exit 0 Exit EndBlock"
   , "0"
  )
  , analtest(
   symbol(internalmod, "last one", [typeint, typeint, typeint, typeint], typeint)
   , "Start(int)%1 8 =(int, int)boolean Br2(1, 2)%4 Exit %1 9 =(int, int)boolean Br2(1, 2)%4 Exit %1 10 =(int, int)boolean Br2(2, 1)%1 11 =(int, int)boolean Br2(1, 2)%4 Exit %1 12 =(int, int)boolean Br2(2, 1)%1 13 =(int, int)boolean Br2(1, 2)%4 Exit %1 14 =(int, int)boolean Br2(1, 2)14 Exit 9 Exit EndBlock"
   , "Start(int)/br
   %1 JmpB 17 8:1 9:1 10:1 11:1 12:1 13:1 14:2:3 Jmp 17 /br
   %4 Exit /br
   14 Exit /br
   9 Exit /br
   EndBlock /br
   "
  )
 ]
for acc = "", test ∈ inputs
do
 let a =
  %.newanal:T(
   tosymbols:T(in.test, self.test)
   , self.test
   , if name.self.test ∉ "loopisnoop" then "tailrecursion" else ""
  ),
 acc
 + if a ≠ out.test then "/p <* literal Fail *>:(self.test)Input::(tosymbols:T(in.test, self.test))Expected::(out.test)got::(a)"
 else "Pass:(self.test)",
acc

type analtest is self:symbol, in:seq.word, out:seq.word

use seq.analtest.T

use symbol1

function tosymbols:T(in:seq.word, self:symbol) seq.symbol
{change seq of words into seq of symbols}
let typegraph = addabstract(typeref."graph graph *", typeword)
let X = "Exit EndBlock 7777 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 %1 %2 %3 %4 %5 %6 %7 %8 %9 %10"
let XR =
 [Exit, EndBlock, Lit.7777]
 + [Lit.0, Lit.1, Lit.2, Lit.3, Lit.4, Lit.5, Lit.6, Lit.7, Lit.8, Lit.9]
 + [Lit.10, Lit.11, Lit.12, Lit.13, Lit.14]
 + [Local.1, Local.2, Local.3, Local.4, Local.5, Local.6, Local.7, Local.8, Local.9, Local.10]
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
  , GtOp
  , Start.typeint
  , Start.typeboolean
  , PlusOp
  , Littrue
  , Litfalse
  , symbol(moduleref("* seq", typeint), "+", [seqof.typeint, seqof.typeint], seqof.typeint)
  , Sequence(typeint, 1)
  , symbol(internalmod, "idxNB", [seqof.typeint, typeint], typeint)
  , Loopblock([seqof.typeint, typeint], 4, typeint)
  , Loopblock([typeint, typeint, typeint], 5, typeint)
  , GetSeqLength
  , symbol(internalmod, "*", [typeint, typeint], typeint)
  , symbol(internalmod, "-", [typeint, typeint], typeint)
 ]
 + self
 + [
  symbol(internalmod, "sinks", [typegraph, seqof.typeword], seqof.typeword)
  , symbol(moduleref("* seq", typeword), "+", [seqof.typeword, seqof.typeword], seqof.typeword)
  , symbol(moduleref("* seq", typeword), "asset", [seqof.typeword], seqof.typeword)
  , Start.seqof.typeint
 ]
for X3 = empty:seq.seq.word, e ∈ X2R
do
 let h = %.e
 {assert 1 #"idxNB"/nin h report h}
 let hh0 = if last.h ∈ "/br" then h >> 1 else h,
 let j = findindex(hh0, ":" sub 1),
 X3 + (if j > n.hh0 then hh0 else hh0 << j)
let inarg = 2
for acc = empty:seq.symbol, arg = "", typ = "", state = 0, w ∈ reverse.in
do
 if w ∈ ")" then next(acc, "", typ, inarg)
 else if w ∈ "(" then next(acc, arg, typ, 0)
 else if state = inarg then next(acc, [w] + arg, typ, inarg)
 else if w ∈ "empty" then
  next(
   [
    symbol4(
     moduleref("* seq", typeint)
     , "empty" sub 1
     , seqof.typeint
     , empty:seq.mytype
     , seqof.typeint
    )
   ]
   + acc
   , arg
   , typ
   , 0
  )
 else if w ∈ "Loop: " then next(acc, arg, "", 0)
 else if isempty.arg ∧ w ∈ "int boolean.seq word graph" then next(acc, arg, [w] + typ, 0)
 else if w ∈ "Define" then next([Define.value.acc sub 1] + acc << 1, arg, typ, 0)
 else if w ∈ "Continue" then next([continue.value.acc sub 1] + acc << 1, arg, typ, 0)
 else if w ∈ "Jmp" then next(acc << 1, arg, typ, 0)
 else if w ∈ ":" then
  if kind.acc sub 1 = kint then
   let v = value.acc sub 1,
   next([Label.v] + acc << 1, arg, typ, 0)
  else next(acc, arg, "", 0)
 else if w ∈ "JmpB" then
  let v = value.acc sub 1 - 1,
  next(Jmp.subseq(acc, 2, v) + acc << v, arg, typ, 0)
 else
  let j = findindex(X, w),
  if isempty.arg ∧ j ≤ n.X then next([XR sub j] + acc, arg, "", 0)
  else
   assert not(isempty.arg ∧ isempty.typ) report "Confusion with Word" + w + "/p" + %.acc
   let t2 = if isempty.arg then %.w + typ else %.w + "(" + arg + ")" + typ
   for i = 1, e ∈ X3 while subseq(t2, 1, n.e) ≠ e do i + 1,
   assert i ≤ n.X3 report "testanal SDF:(w)(:(arg)):(typ)/br:(in)",
   next([X2R sub i] + acc, "", "", 0)
for xx = "", w ∈ %.acc do if w ∈ "/br" then xx else xx + w
assert xx = in report "DIFF:(in)/p:(xx)",
acc

use seq1.word

use seq1.seq.word 