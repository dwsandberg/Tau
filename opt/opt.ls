Module opt

use bits

use callconfig

use compilerfrontT.callconfig

use encoding.exp

use otherseq.encoding.exp

use otherseq.Exp

use stack.Exp

use otherseq.exp

use seq.exp

use stack.exp

use file

use otherseq.int

use set.int

use otherseq.loc

use set.loc

use standard

use symbol

use otherseq.symbol

use seq.symbol

use set.symbol

use symbol2

use otherseq.symdef

use seq.symdef

use set.symdef

use set.word  

Function test(input:seq.file, o:seq.word) seq.file {OPTION PROFILE}
let m = compilerFront:callconfig("pass2", input)
let mm=hasstate.prg.m
let output=for  acc="",   sd /in toseq.mm do
 if  name.sym.sd /in "setinsert" then 
   let a=(GG.asset.[sd])_1
   acc+"$(sym.sd)  $(code.sd) /p $(code.a)"
 else acc
 /for(acc)
 [file(o,output )]

[file(o, %.cardinality.newprg+profileresults."time")]

 + {%.toseq.mm} %n.encodingdata:exp 
[file(o, output)]

Function hasstate(prg:set.symdef) set.symdef
let inithasstate = 
 asset.[symbol(internalmod, "addencoding", [typeint, typeptr, typeint, typeint], typeint)
  , symbol(internalmod, "getinstance", typeint, typeptr)
  , symbol(moduleref("* builtin", typereal), "assert", seqof.typeword, typereal)
  , symbol(moduleref("* builtin", typeptr), "assert", seqof.typeword, typeptr)
  , symbol(moduleref("* builtin", typeint), "assert", seqof.typeword, typeptr)]
let hasstate = hasstate(inithasstate, toseq.prg )
 for acc = empty:set.symdef, sd ∈ toseq.prg  do
  {if isabstract.module.sym.sd then   acc else }
  let options = getOptions.sd
  assert isempty(asset.options \ asset."COMPILETIME NOINLINE PROFILE INLINE STATE
  VERYSIMPLE ThisLibrary") report "SDFSDF"+options
  let newOptions = 
   options + if sym.sd ∈ hasstate then "STATE" else "" /if
   + if not.isempty.code.sd ∧ "NOINLINE"_1 ∉ options
   ∧ isverysimple(nopara.sym.sd, code.sd) then
    "VERYSIMPLE"
   else
    "" 
  if options = newOptions then
   acc+ sd 
  else
   acc + symdef4(sym.sd, code.sd, paragraphno.sd, newOptions)
 /for (
  for acc2 = acc, sym ∈ toseq.inithasstate do
   acc2 + symdef4(sym, empty:seq.symbol, 0, "STATE")
  /for (acc2)
 ) 

Function  GG(mm:set.symdef)  set.symdef
 for acc = empty:set.symdef, sd ∈ toseq.mm do
   if  { %.sym.sd=" parsersupport.bindinfo:last (reduction.bindinfo) bindinfo" /and}    length.code.sd > 0  
    then
   {assert     length.acc < 40750  report "XXX"+%.length.acc+%.sym.sd+%.code.sd }
    let b = {checkTailRecursion(C(code.sd, mm), sym.sd)}
           C(code.sd, mm)
   let b3 = FF.b 
  { assert false report "$(sym.sd) $(getOptions.sd) $(code.sd) /p $(b) /p $(b3) /p" 
   +%n.encodingdata:exp } 
   acc  +symdef4(sym.sd,b3,paragraphno.sd,getOptionsBits.sd)
  else 
   acc+sd
 /for (acc)
 
 
use symbol

function check(code:seq.symbol, hasstate:set.symbol) boolean
if last.code ∈ hasstate then
 for acc = true, sy ∈ code >> 1 while acc do acc = sy ∉ hasstate /for (not.acc)
else
 true

function %(a:symdef) seq.word "/p $(getOptions.a) $(sym.a) $(paragraphno.a)"

function >1(a:exp, b:exp) ordering sym.a >1 sym.b

type exp is sym:symbol, args:seq.Exp,bits:bits

function exp(sym:symbol, args:seq.Exp) exp
     exp(sym,args,if not.isconst.sym /and name.sym /in "DEF2" then SymHasStateFlag else 0x0)

use set.exp

type Exp is bits:bits

function flagsNo int 4

function  ConstFlag bits 0x1

function  LocalFlag bits 0x2

function  SymHasStateFlag bits 0x4

function uses(e:Exp ) set.Exp
if isConst.e /or isLocal.e then empty:set.Exp
else uses(e,empty:set.Exp,false)

function avail(e:Exp) set.Exp
if isConst.e /or isLocal.e then empty:set.Exp
else uses(e,empty:set.Exp,true)

function avail(s:seq.Exp) set.Exp
  for  acc=empty:set.Exp,    b /in s do 
      if isConst.b /or isLocal.b   then acc
      else acc /cup uses(b,acc,true)
  /for(acc) 

function uses(e:Exp,k:set.Exp,avail:boolean) set.Exp
let a=toexp.e 
     let t=   if avail then
          if isloopblock.sym.a then args.a >> 1
          else if isbr.sym.a then 
          { ???? only includes branch condition but loop contains defs too}
            [ (args.a)_(length.args.a-2)]
          else args.a
        else args.a
  for  acc=k+e,    b /in t do 
      if isConst.b /or isLocal.b /or b /in k  then acc
      else acc /cup uses(b,acc,avail)
  /for(acc) 

use set.Exp

function >1(a:Exp,b:Exp) ordering  toint.bits.a >1 toint.bits.b

function flags(a:exp) bits   if islocal.sym.a then LocalFlag
else if isconst.sym.a /or (isSequence.sym.a /or isRecord.sym.a) /and allconst.a 
then ConstFlag
else bits.a

function allconst(a:exp) boolean
  for  acc=true,    e /in args.a while acc do
     isConst.e 
  /for(acc)
     
function isConst(e:Exp) boolean
   (bits.e /and ConstFlag ) /ne 0x0
 
function isLocal(e:Exp) boolean
   (bits.e /and LocalFlag ) /ne 0x0
   
   function isDEF2(e:Exp) boolean
   (bits.e /and SymHasStateFlag ) /ne 0x0

 

function toexp(a:Exp) exp decode.to:encoding.exp(toint.(bits.a >> flagsNo ))

function toExp(a:exp) Exp Exp(bits.valueofencoding.encode.a << flagsNo /or flags.a)


function =(a:Exp, b:Exp) boolean bits.a = bits.b

function =(a:exp, b:exp) boolean sym.a = sym.b ∧ args.a = args.b

function hash(e:exp) int  
 for acc=hash(hashstart,hash.worddata.sym.e), a /in args.e do
    hash(acc,toint.bits.a)
 /for(finalmix.acc) 

use xxhash 

function toSeqExp(a:seq.exp) seq.Exp 
for acc = empty:seq.Exp, e ∈ a do acc + toExp.e /for (acc)


function %(a:Exp) seq.word  if false then "{$(toint.bits.a)}"
else
let e = toexp.a 
%.args.e + %.sym.e + if isempty.args.e then "" else "{$(toint.bits.a)}"



function removeStart(e:exp) Exp
if   isExit.sym.e then
 let t = first.args.e
 let b = toexp.t
 if isstart.sym.b then first.args.b else t
else
 {assert isconst.sym.e ∨ islocal.sym.e report" XX"+%.sym.e}
 if isstart.sym.e ∨ isExit.sym.e  then first.args.e else toExp.e

function %(e:exp) seq.word  "expression $(name.sym.e) [ $( %n( args.e)) ]"
  
%.toExp.e

use stack.seq.exp

 function HH( s:seq.Exp ,b:set.Exp,result:seq.Exp) seq.Exp
   {we do not want to move calculation done in an outer to
   and inner basic block.  This figures out which  
     calculations are not used in the inter block and removes them}
   if isempty.s then result
   else 
    let e=last.s
      if e /in b then HH(s >> 1, b \ avail(e),[e]+result  ) 
    else if isConst.e /or isLocal.e  then HH(s >> 1,b,result)
    else 
     let c=toexp.e 
     HH( s >> 1+if isloopblock.sym.c then  args.c >> 1 
     else if isbr.sym.c then   [first.args.c ]
     else args.c,b,result)
   
    

function C(code:seq.symbol, mm:set.symdef) Exp 
let PreFref0 =PreFref
for blkstk = empty:seq.symbol
 , cnt = {????}1
 , pre = empty:seq.Exp
 , stk = empty:stack.exp
 , locals = empty:set.exp
 , last=Lit.1
 , sy ∈ code
do
 {assert length.blkstk < 75 report "XX"+%.length.code+%.blkstk+
 "/p /p"+%(code << length.blkstk)}
 if isconst.sy then  
   next(blkstk+sy, cnt, pre, push( stk, exp(sy,empty:seq.Exp)), locals,sy)
 else  if last=PreFref0 then
   next(blkstk+sy, cnt, pre, push( stk, exp(Fref.sy,empty:seq.Exp)), locals,sy)
 else  if isspecial.sy then 
   if sy =PreFref0 then 
     next(blkstk, cnt, pre, stk, locals,sy) 
  else if sy = EndBlock then
  let parts = 
   for stk2 = stk, acc = empty:seq.exp, x ∈ constantseq(length.toseq.stk, 0)
   while not.isstartorloop.sym.top.stk2
   do
    let blocksym = sym.top.stk2
    if  isExit.blocksym ∨ iscontinue.blocksym  then
     next(pop.stk2, [top.stk2] + acc)
    else
      assert isbr.blocksym report "DSF $(blocksym) " +%.code+%n.toseq.stk
      let used=uses.toExp.acc_(brt.blocksym) /cup uses.toExp.acc_(brf.blocksym)
           \ avail.last.args.top.stk2
     next(pop.stk2
      , [
        exp(blocksym
         , HH(args.top.stk2 >> 1, used, empty:seq.Exp) + last.args.top.stk2
         + removeStart.acc_(brt.blocksym)
         + removeStart.acc_(brf.blocksym))
        ]
      + acc)
   /for (   let body=toExp.first.acc
       let args=args.top.stk2
       let defs=  args >> nopara.sym.top.stk2
     let newargs= if isempty.defs then args+body
      else 
        let loopargs= args << length.defs
       let used=uses.body \ avail(loopargs)
        HH(defs,used,empty:seq.Exp)+loopargs+ body
    push(pop(stk2), exp(sym.top.stk2, newargs))
   )
  next(blkstk+sy, cnt, empty:seq.Exp, parts, locals,sy)
 else if isdefine.sy then
  if  islocal.sym.top.stk /or isconst.sym.top.stk then
  next(blkstk+sy, cnt, pre, pop.stk, locals + exp(Local.value.sy, [toExp.top.stk]),sy)
  else 
  let argx = [{?}toExp.top.stk, toExp.exp(Lit.cnt, empty:seq.Exp)]
    next(blkstk+sy 
    , cnt 
    ,   pre+toExp.top.stk
    , pop.stk
    , locals + exp(Local.value.sy, [toExp.top.stk]),sy)
 else if islocal.sy ∧ not.isempty.lookup(locals, exp(sy, empty:seq.Exp)) then
  let a = lookup(locals, exp(sy, empty:seq.Exp))
  next(blkstk+sy, cnt, pre, push(stk, toexp.first.args.a_1), locals,sy)
 else if isstart.sy then
  next(blkstk+sy, cnt, pre, push(stk, exp.sy), locals,sy)
  else  if isbr.sy /or isloopblock.sy then
    let exp = {?}exp(sy, pre+toSeqExp.top(stk, nopara.sy))
     next(blkstk+sy,cnt,empty:seq.Exp,push(pop(stk, nopara.sy), exp),locals,sy)
 else if sy=Exit   then
  next(blkstk+sy,cnt,empty:seq.Exp,push(pop(stk), exp(Exit,[wrappre(stk,pre)])),locals,sy)
 else 
       let exp = {?}exp(sy, toSeqExp.top(stk, nopara.sy))
   next(blkstk+sy, cnt, pre, push(pop(stk, nopara.sy), exp), locals,sy)
  else 
  let sd = getSymdef(mm, sy)
  if not.isempty.sd ∧ hasState.sd_1 then
   let argx = [{?}toExp.exp(sy, toSeqExp.top(stk, nopara.sy)), toExp.exp(Lit.cnt, empty:seq.Exp)]
   let expx=exp(symbol(internalmod, "DEF2", typeint),argx)
    next(blkstk+sy
    , cnt + 1
    , pre+toExp.expx
    , push(pop(stk, nopara.sy), expx)
    , locals,sy)
  else
   let exp = {?}exp(sy, toSeqExp.top(stk, nopara.sy))
   next(blkstk+sy, cnt, pre, push(pop(stk, nopara.sy), exp), locals,sy)
/for (wrappre(stk,pre))



function  wrappre(stk:stack.exp,pre:seq.Exp) Exp
   toExp.if isempty.pre then top.stk
   else exp(symbol(internalmod, "DEF", typeint), pre + toExp.top.stk)

type result is code:seq.symbol, places:seq.place, parts:seq.Exp, fixes:seq.loc

function result( code:seq.symbol, places:seq.place,  fixes:seq.loc) result
 result(code , places , empty:seq.Exp, fixes )

type place is exp:Exp, idx:int

use otherseq.place

use otherseq.mytype

function =(a:place, b:place) boolean exp.a = exp.b

function %(p:place) seq.word  "["+%.toint.bits.exp.p+%.idx.p+"]"

function FF(e:Exp) seq.symbol
let r = FF(e, empty:seq.symbol, empty:seq.place, empty:seq.loc, true)
for acc = code.r,  f ∈ toseq.asset.fixes.r   do
   subseq(acc, 1, loc.f) + Define(100 + loc.f) + Local(100 + loc.f)
   + acc << loc.f
/for (acc)

function addExit(s:seq.symbol) seq.symbol
if isExit.last.s ∨ iscontinue.last.s then s else s + Exit


function FF(e:Exp, codein:seq.symbol, placein:seq.place, infixes:seq.loc, share:boolean) result
let i = if share then findindex(placein, place(e, 0)) else length.placein + 1
if i ≤ length.placein then
  let idx=idx.placein_i
 result(codein + Local(100 + idx)
  , placein
  , if idx < length.codein /and isdefine.codein_(idx+1) then infixes else  infixes + loc(idx.placein_i ))
else
 let d = toexp.e
   if isconst.sym.d then
   result(codein+sym.d,placein,infixes)
  else if isstart.sym.d then
  let r = FF(first.args.d, codein + sym.d, placein, infixes, true)
  result(code.r + EndBlock, places.r + place(e, length.code.r + 1),   fixes.r)
  else if isbr.sym.d then
   let z= args.d << (length.args.d -3)
   let r = if length.args.d > 3 then
   let r1=defs(args.d >> 3,codein, placein, infixes,true)
       FF(first.z, code .r1, places.r1,  fixes.r1, true)
   else 
    FF(first.z, codein, placein, infixes, true)
  let r2 = FF((z)_2, code.r + Br2(1, 2), places.r, fixes.r, true)
  let r3 = FF((z)_3, addExit.code.r2, places.r, fixes.r2, true)
    let partsTrue =  if last.code.r2=Exit then  parts.r2 else [z_2]
  let partsFalse =  if last.code.r3=Exit then  parts.r3 else [z_3]
 let idxtrue= findindex(partsFalse,z_2)  
     if   idxtrue /le  length.partsFalse then 
 let r4= FF(z_3, code.r+Br2(idxtrue,   1), places.r, fixes.r, true)
   result(addExit.code.r4, placein, [e]+  partsFalse  , fixes.r4)
   else
  let tmp = 
   if brf.sym.d = length(partsTrue) +1  then
    code.r3
   else
    code.r + Br2(1, length(partsTrue) +1 ) + code.r3 << (length.code.r + 1)
  result(addExit.tmp, placein, [e]+ partsTrue + partsFalse  , fixes.r3)
 else if name.sym.d ∈ "DEF2" then
  let r = FF(first.args.d, codein, placein, infixes, false)
  result(code.r, places.r + place(e, length.code.r),   fixes.r)
 else if name.sym.d ∈ "DEF" then
   let r0= defs(args.d >> 1,codein, placein, infixes,false)
   FF(last.args.d, code.r0, places.r0, fixes.r0, false)
 else if isloopblock.sym.d then
  let body=last.args.d
  let defs=args.d >> (nopara.sym.d+1)
  let params=subseq(args.d,length.defs+1,length.args.d-1)
  let r0= defs(defs,codein,placein,infixes,true)
  for code = code.r0, place = places.r0, fixes = fixes.r0, a ∈ params do
   let r = FF(a, code, place, fixes, true)
   next(code.r, places.r, fixes.r)
  /for (
   let r = FF(body, code + sym.d, place, fixes, true)
   result(code.r + EndBlock, places.r + place(e, length.code.r + 1),  fixes.r)
  )
 else
  for code = codein, place = placein, fixes = infixes, a ∈ args.d do
   {assert toint.bits.e /in [96,64,32,18] report  %.e+"/p"+%.a
    +"places"+%.place+"fixes:"+%.fixes}
   let r = FF(a, code, place, fixes, true)
   next(code.r, places.r, fixes.r)
  /for ( 
   result(code + sym.d
    , if isempty.args.d ∨ not.share then place else place + place(e, length.code + 1)
    , fixes)
  )
  
  function defs(defs:seq.Exp, codein:seq.symbol, placein:seq.place, infixes:seq.loc,all:boolean) result
       for code = codein, place = placein, fixes = infixes, a ∈ defs do
        if all /or isDEF2.a then 
        let r = FF(a, code, place, fixes, true)
       next(code.r+Define(100+length.code.r), places.r, fixes.r)
       else next(code,place,fixes)
  /for (result (code,place,fixes))
       

type loc is loc:int 

function >1(a:loc,b:loc) ordering  loc.b >1 loc.a

function %(a:loc) seq.word %.loc.a  

function exp(s:symbol) exp exp(s, empty:seq.Exp)

_____________________

function checkTailRecursion(e:Exp, this:symbol) Exp
let d = toexp.e
if not.isstart.sym.d then
 e
else
 let t = expandBlock(toexp.first.args.d, this)
 if t = first.args.d then
  e
 else
  for acc = empty:seq.Exp, i ∈ arithseq(nopara.this, 1, 1) do
   acc + toExp.exp.Local.i
  /for (
   toExp.exp(Loopblock(paratypes.this, nopara.this + 1, resulttype.this)
    , acc + adjust(t, nopara.this))
  )

Function adjust(e:Exp, val:int) Exp
{???? need to handle loopblock}
let d = toexp.e
if islocal.sym.d then
 toExp.exp.Local(value.sym.d + val)
else
 for acc = empty:seq.Exp, a ∈ args.d do acc + adjust(a, val) /for ({?}toExp.exp(sym.d, acc))

Function expandBlock(d:exp, this:symbol) Exp
assert isbr.sym.d report "???"
let argt=(args.d)_(length.args.d-1)
let argf=last.args.d
let bt = toexp.argt
let bf = toexp.argf
let newbt = 
 if isbr.sym.bt then
  expandBlock(bt, this)
 else if this = sym.bt then toExp.exp(continue.nopara.this, args.bt) else argt
let newbf = 
 if isbr.sym.bf then
  expandBlock(bf, this)
 else if this = sym.bf then toExp.exp(continue.nopara.this, args.bf) else argf
toExp.exp(sym.d,   args.d >> 2+[ newbt, newbf])

function isverysimple(nopara:int, code:seq.symbol) boolean
if code = [Local.1] ∧ nopara = 1 then
 true
else
 for isverysimple = length.code ≥ nopara, idx = 1, sym ∈ code
 while isverysimple
 do
  next(
   if idx ≤ nopara then
    sym = Local.idx
   else
    not.isbr.sym ∧ not.isdefine.sym ∧ not.islocal.sym
   , idx + 1)
 /for (isverysimple)

function hasstate(hasstate:set.symbol, unknown:seq.symdef) set.symbol
 let PreFref0=PreFref
for hasstate0 = hasstate, acc = empty:seq.symdef, sd ∈ unknown do
 if  name.sym.sd ∈ "makereal" ∧ %.sym.sd = "real:makereal (seq.word) real" then
  next(hasstate0, acc)
 else
  let options = getOptions.sd
  if "STATE"_1 ∈ options then
   next(hasstate0 + sym.sd, acc)
  else
   let nostate = 
    for nostate = true, last = Lit.0, sy ∈ code.sd
    while nostate
    do  
     next(if  isspecial.sy  /or sy = sym.sd ∨ last = PreFref0 then nostate 
      else  not.isGlobal.sy /and sy ∉ hasstate , sy)
    /for (nostate)
   if nostate then next(hasstate0, acc + sd) else next(hasstate0 + sym.sd, acc)
/for (if length.acc = length.unknown then hasstate else hasstate(hasstate0, acc)) 