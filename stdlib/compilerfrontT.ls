Module compilerfrontT.T

use UTF8

use bits

use compilerfront

use localmap2

use mergeblocks

use pass2

use real

use standard

use symbol

use symbolconstant

use typedict

use seq.char

use otherseq.int

use seq.int

use set.int

use set.localmap2

use otherseq.mytype

use seq.mytype

use otherseq.symbol

use seq.symbol

use set.symbol

use seq.symdef

use set.symdef

use otherseq.word

use set.word

use otherseq.seq.int

use seq.seq.int

use seq.seq.symbol

use seq.seq.word

use set.seq.word

use seq.seq.seq.symbol

Function compilerfront2:T(option:seq.word, allsrc:seq.seq.word, libinfo:midpoint)midpoint
{OPTION PROFILE}
let m = compilerfront3(option, allsrc, libinfo)
if first.option.m ∈ "library text pass1"then m
else
 let prg5 = pass2:T(prg.m, typedict.m, "") ∪ templates.m
 if option = "all2"then prepareback(prg5, m, libinfo)
 else midpoint(option, prg5, typedict.m, libmods.m, src.m)

unbound interpretCompileTime:T(args:seq.symbol, ctsym:symbol, typedict:typedict)seq.symbol

Function pass2:T(knownsymbols0:set.symdef, t:typedict, option:seq.word)set.symdef
{OPTION PROFILE}
let knownsymbols = 
 for acc2 = empty:set.symdef, pele0 ∈ toseq.knownsymbols0 do
  acc2
  + if isempty.code.pele0 then pele0
  else
   for acc = [first.code.pele0], last = first.code.pele0, c ∈ code.pele0 << 1 do
    next(if last = PreFref then acc >> 1 + Fref.c else acc + c, c)
   /for(symdef(sym.pele0, acc, paragraphno.pele0))
 /for(acc2)
if option = "addpass"then additionalpass:T(toseq.knownsymbols, knownsymbols, t)
else
 subpass2:T(empty:seq.symdef, empty:set.symdef, asset.renumberconstants.toseq.knownsymbols, 0, t)
 ∪ constantsymbols

function subpass2:T(bigin:seq.symdef, corein:set.symdef, toprocess:set.symdef, count:int, typedict:typedict)set.symdef
{OPTION PROFILE}
{assert count < 4 report"SIZE"+%.length.toseq.toprocess+%.length.bigin+%.length.toseq.corein+print.count}
for big = bigin, small = empty:set.symdef, core = corein, pele0 ∈ toseq.toprocess do
 let pele = 
  {if count > 0 /or isempty.code.pele0 then pele0 else for acc=empty:seq.symbol, last=first. code.pele0, c /in code.pele0 
<< 1 do next(acc+if last=PreFref then Fref.c else last, c)/for(symdef(sym.pele0, acc+c, paragraphno.pele0))}
  pele0
 let s = sym.pele
 let fullcode = code.pele
 let options = getoption.fullcode
 let code = removeoptions.fullcode
 if isempty.code ∨ "VERYSIMPLE"_1 ∈ options ∨ "INLINE"_1 ∈ options then
  next(big, small, pele ∪ core)
 else if"COMPILETIME"_1 ∈ options then
  let code4 = firstopt:T(core, s, fullcode, options, true, typedict)
  next(big, small, symdef(s, code4, paragraphno.pele) ∪ core)
 else if length.code < 30 then
  let t = firstopt:T(core, s, fullcode, options, true, typedict)
  if"INLINE"_1 ∈ getoption.t then next(big, small, symdef(s, t, paragraphno.pele) ∪ core)
  else next(big, symdef(s, t, paragraphno.pele) ∪ small, core)
 else next(big + pele, small, core)
/for(if length.toseq.corein = length.toseq.core then
 additionalpass:T(toseq.core + toseq.small + big, core, typedict)
else subpass2:T(big, core, small, count + 1, typedict)/if)

Function additionalpass:T(p:seq.symdef, start:set.symdef, typedict:typedict)set.symdef
{OPTION PROFILE}
for acc = start, prgele ∈ p do
 let code3 = code.prgele
 let sym3 = sym.prgele
 if isempty.code3 then prgele ∪ acc
 else
  symdef(sym3, firstopt:T(acc, sym3, code3, getoption.code3, false, typedict), paragraphno.prgele)
  ∪ acc
/for(acc)

Function firstopt:T(p:set.symdef, s:symbol, code:seq.symbol, options:seq.word, first:boolean, typedict:typedict)seq.symbol
let pdict = 
 for pmap = empty:set.localmap2, parano ∈ arithseq(nopara.s, 1, 1)do pmap + localmap2(parano, [Local.parano])/for(pmap)
let a = xxx:T(p, removeoptions.code, s, pdict, typedict)
let t = 
 if first then a
 else if Hasfor ∈ flags.a ∨ Callself ∈ flags.a then
  let ty = if Hasfor ∈ flags.a then expandforexp(code.a, nextvar.a)else code.a
  let t2 = 
   if Callself ∈ flags.a ∧ {????}wordname.s ≠ "subpass2"_1 then optB(ty, s, reorgwhen)
   else ty
  expandresult(nextvar.a, t2, flags.a)
 else a
let newoptions1 = 
 if between(length.code.t, 1, 21) ∧ Callself ∉ flags.t ∧ Hasfor ∉ flags.t
 ∧ "NOINLINE"_1 ∉ options then
  if isverysimple(nopara.s, code.t)then"INLINE VERYSIMPLE"else"INLINE"
 else""
let newoptions = 
 if isempty.options then newoptions1
 else if options = newoptions1 then options
 else toseq(asset.options \ asset."VERYSIMPLE" ∪ asset.newoptions1)
if newoptions = ""then code.t else code.t + Words.newoptions + Optionsym

function xxx:T(p:set.symdef, code:seq.symbol, s:symbol, pdict:set.localmap2, typedict:typedict)expandresult
let a = scancode:T(p, code, nopara.s + 1, pdict, s, typedict)
let new = if Hasmerge ∈ flags.a then optB(code.a, Lit.1, reorgwhen)else code.a
if length.code = length.new ∧ length.code > 20 ∨ new = code then expandresult(nextvar.a, new, flags.a)
else xxx:T(p, new, s, pdict, typedict)

Function scancode:T(p:set.symdef, org:seq.symbol, nextvarX:int, mapX:set.localmap2, self:symbol, typedict:typedict)expandresult
for flags = bits.0, result = empty:seq.symbol, nextvar = nextvarX, map = mapX, sym ∈ org do
 let len = length.result
 if isconst.sym then next(flags, result + sym, nextvar, map)
 else if isspecial.sym then
  if isdefine.sym then
   let thelocal = value.sym
   if len > 0 ∧ (isconst.result_len ∨ islocal.result_len)then
    next(flags
    , subseq(result, 1, length.result - 1)
    , nextvar
    , localmap2(thelocal, [result_len]) ∪ map
    )
   else next(flags, result + Define.nextvar, nextvar + 1, localmap2(thelocal, [Local.nextvar]) ∪ map)
  else if isbr.sym then
   let hasnot = last.result = NotOp
   let sym1 = if hasnot then Br2(brf.sym, brt.sym)else sym
   let result1 = if hasnot then result >> 1 else result
   let newsym = 
    if last.result1 = Litfalse then Br2(brf.sym1, brf.sym1)
    else if last.result1 = Littrue then Br2(brt.sym1, brt.sym1)else sym1
   next(if brt.newsym = brf.newsym ∨ isblock.last.result1 then Hasmerge ∨ flags else flags
   , result1 + newsym
   , nextvar
   , map
   )
  else if sym = Exit ∧ isblock.last.result then next(flags ∨ Hasmerge, result + sym, nextvar, map)
  else if isloopblock.sym then
   let nopara = nopara.sym
   let addlooplocals = 
    for pmap = map, parano = 1, e ∈ constantseq(10000, 1)
    while parano ≤ nopara
    do next(localmap2(firstvar.sym + parano - 1, [Local(nextvar + parano - 1)]) ∪ pmap, parano + 1)
    /for(pmap)
   next(flags
   , result + Loopblock(paratypes.sym, nextvar, resulttype.sym)
   , nextvar + nopara
   , addlooplocals
   )
  else if isRecord.sym ∨ isSequence.sym then
   let nopara = nopara.sym
   let args = subseq(result, len + 1 - nopara, len)
   let constargs = for acc = true, @e ∈ args while acc do isconst.@e /for(acc)
   if constargs then next(flags, subseq(result, 1, len - nopara) + Constant2(args + sym), nextvar, map)
   else next(flags, result + sym, nextvar, map)
  else if islocal.sym then
   let t = lookup(map, value.sym)
   next(flags, result + if isempty.t then[sym]else value.t_1, nextvar, map)
  else next(flags, result + sym, nextvar, map)
 else if sym = NotOp ∧ last.result = NotOp then next(flags, result >> 1, nextvar, map)
 else if length.result > 2 ∧ isconst.last.result ∧ ismember.sym then
  let arg = result_(-2)
  let nonew = islocal.arg ∨ isconst.arg
  let z = seqelements.last.result
  let var = if nonew then arg else Local.nextvar
  let newcode = 
   if isempty.z then[Litfalse]
   else if length.z = 1 then[var, first.z, EqOp]
   else
    let t = length.z + 2
    for acc = [Start.typeboolean], idx = 2, w ∈ z >> 1 do next(acc + [var, w, EqOp] + Br2(t - idx, 1), idx + 1)/for(acc + [var, last.z, EqOp, Exit, Littrue, Exit, EndBlock])
  {let newcode=removeismember(last.result, if nonew then arg else Local.nextvar)}
  if nonew then next(flags, result >> 2 + newcode, nextvar, map)
  else next(flags, result >> 1 + Define.nextvar + newcode, nextvar, map)
 else if wordname.sym ∈ "forexp" ∧ isBuiltin.sym then
  let noop = forexpisnoop(sym, result)
  if not.isempty.noop then next(flags, noop, nextvar, map)
  else next(flags ∨ Hasfor, result + sym, nextvar, map)
 else if wordname.sym ∈ "indexseq45" ∧ isInternal.sym then
  next(flags ∨ Hasfor, result + sym, nextvar, map)
 else if sym = self then next(flags ∨ Callself, result + sym, nextvar, map)
 else
  let nopara = nopara.sym
  let dd = getCode(p, sym)
  let options = getoption.dd
  let compiletime = 
   if first."COMPILETIME" ∉ options ∧ (name.sym ∉ "_" ∨ nopara ≠ 2)then empty:seq.symbol
   else
    let args = subseq(result, len - nopara + 1, len)
    interpretCompileTime:T(subseq(result, len - nopara + 1, len), sym, typedict)
  if not.isempty.compiletime then
   let newconst = if length.compiletime > 1 then Constant2.compiletime else first.compiletime
   next(flags, result >> nopara + newconst, nextvar, map)
  else if first."VERYSIMPLE" ∈ options then
   next(flags, result + removeoptions.dd << nopara.sym, nextvar, map)
  else if"INLINE"_1 ∉ options then
   let newflags = 
    if"STATE"_1 ∈ options ∨ {wordname.sym ∈"setfld"∨}isGlobal.sym then State ∨ flags
    else flags
   next(newflags, result + sym, nextvar, map)
  else
   let code = removeoptions.dd
   if isempty.code then next(flags, result + sym, nextvar, map)
   else if length.code = 1 ∧ code = [Local.1] ∧ nopara = 1 then
    {function just returns result}next(flags, result, nextvar, map)
   else
    let t = backparse2(result, len, nopara, empty:seq.int) + [len + 1]
    {assert length.t=nopara+1 report"INLINE PARA PROBLEM"}
    let new = expandinline:T(result, t, nextvar, code, p, self, typedict)
    next(flags ∨ flags.new, subseq(result, 1, t_1 - 1) + code.new, nextvar.new, map)
/for(expandresult(nextvar, result, flags))

function expandinline:T(result:seq.symbol, t:seq.int, nextvarin:int, code:seq.symbol, p:set.symdef
, self:symbol, typedict:typedict)expandresult
for pmap = empty:set.localmap2
, paracode = empty:seq.symbol
, nextvar = nextvarin
, parano = 1
, lastidx = t_1
, idx ∈ t << 1
do
 next(pmap + localmap2(parano, [Local.nextvar])
 , paracode + subseq(result, lastidx, idx - 1) + Define.nextvar
 , nextvar + 1
 , parano + 1
 , idx
 )
/for(let r = scancode:T(p, code, nextvar, pmap, self, typedict)
expandresult(nextvar.r, paracode + code.r, flags.r)) 