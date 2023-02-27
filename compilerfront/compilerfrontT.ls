Module compilerfrontT.T

use compileTimeT.T

use addprofile

use bits

use seq.byte

use compilerfront

use file

use seq.int

use localmap2

use set.localmap2

use mergeblocks

use objectio.midpoint

use seq.midpoint

use seq.modExports

use seq.mytype

use seq.seq.mytype

/use opt

use pass2

use standard

use symbol

use seq.symbol

use symbol2

use symbolconstant

use seq.symdef

use set.symdef

use textio

use seq.seq.word

use set.word

Function compilerFront:T(option:seq.word, input:seq.file) midpoint
{OPTION PROFILE}
for libinfo = empty:midpoint, data = empty:seq.byte, i ∈ input do
 if ext.fn.i ∈ "libinfo" then
  let new = first.inbytes:midpoint(data.i),
  next(
   midpoint(""
    , prg.libinfo ∪ prg.new
    , emptytypedict
    , libmods.libinfo + libmods.new
    , empty:seq.seq.word)
   , data)
 else
  next(libinfo, data + [tobyte.10, tobyte.10] + data.i)
/do
 let allsrc = breakparagraph.data
 let libname = extractValue(first.allsrc, "Library")_1
 let EPname = merge.[libname, "$EP"_1]
 let allsrc1 = 
  if length.first.allsrc < 8 ∨ first.first.allsrc ∉ "Library" then
   allsrc
  else
   [first.allsrc + EPname] + allsrc << 1
   + breakparagraph.data.file("??.ls", "Module $(EPname) $(modEntry.allsrc << 2)")
 let m = compilerfront3(option, allsrc1, libinfo),
 if first.option.m ∈ "library text pass1 pass1a prebind" then
  m
 else
  let librarymap = [libname, first."*"]
  let prg = {if" xxx"_1 ∈ option then GG.hasstate.prg.m else} prg.m
  let prg5 = pass2:T(librarymap, prg, typedict.m, option, libname)
  let m2 = 
   if "profile"_1 ∈ option then
    let profinit = symbol(moduleref.[libname, "initialize"_1], "initProfile", typeptr)
    let profdata = symbol(moduleref.[libname, "initialize"_1], "profileData", typeptr)
    let prg6 = addprofile(prg5, libname),
    if isempty.prg6 then
     m
    else
     midpoint5(option
      , prg6 ∪ prg5
      , templates.m
      , typedict.m
      , libmods.m + modExports(module.profinit, [profinit, profdata], empty:seq.seq.mytype)
      , [first.src.m + "initialize"] + src.m << 1)
   else
    midpoint5(option, prg5, templates.m, typedict.m, libmods.m, src.m)
  ,
  if "bitcode"_1 ∈ option then
   let m3 = prepareback(m2, libinfo),
   midpoint5(option.m3, prg.m3, templates.m3, typedict.m3, libmods.m3, src.m3 + allsrc)
  else
   m2

use makeentry

unbound interpretCompileTime:T(librarymap:seq.word, args:seq.symbol, ctsym:symbol, typedict:typedict) seq.symbol

Function pass2:T(librarymap:seq.word
 , knownsymbols0:set.symdef
 , t:typedict
 , option:seq.word
 , libname:word) set.symdef
{OPTION PROFILE}
for knownsymbols = empty:set.symdef, pele0 ∈ toseq.knownsymbols0 do
 if isempty.code.pele0 then
  knownsymbols + pele0
 else
  let code = code.pele0,
  for acc = [first.code], last = first.code, c ∈ code << 1 do
   next(if last = PreFref then acc >> 1 + Fref.c else acc + c, c)
  /do
   let sd = symdef4(sym.pele0, acc, paragraphno.pele0, getOptions.pele0),
   if isrecordconstant.sym.sd then
    let discard = registerConstant.sd,
    knownsymbols
   else
    knownsymbols + sd
/do
 if "addpass"_1 ∈ option then
  additionalpass:T(librarymap, toseq.knownsymbols, knownsymbols, t, libname)
 else
  subpass2:T(librarymap, empty:seq.symdef, empty:set.symdef, knownsymbols, 0, t, libname)
  ∪ constantsymbols.libname

function subpass2:T(librarymap:seq.word
 , bigin:seq.symdef
 , corein:set.symdef
 , toprocess:set.symdef
 , count:int
 , typedict:typedict
 , libname:word) set.symdef
{OPTION XPROFILE}
for big = bigin, small = empty:set.symdef, core = corein, pele ∈ toseq.toprocess do
 let s = sym.pele
 let code = code.pele,
 if isempty.code ∨ isVERYSIMPLE.pele ∨ isINLINE.pele then
  next(big, small, pele ∪ core)
 else if isCOMPILETIME.pele then
  next(big, small, firstopt:T(librarymap, core, pele, true, typedict, libname) ∪ core)
 else if length.code < 30 then
  let t = firstopt:T(librarymap, core, pele, true, typedict, libname),
  if isINLINE.t then next(big, small, t ∪ core) else next(big, t ∪ small, core)
 else
  next(big + pele, small, core)
/do
 if length.toseq.corein = length.toseq.core then
  additionalpass:T(librarymap, toseq.core + toseq.small + big, core, typedict, libname)
 else
  subpass2:T(librarymap, big, core, small, count + 1, typedict, libname)

Function additionalpass:T(librarymap:seq.word
 , p:seq.symdef
 , start:set.symdef
 , typedict:typedict
 , libname:word) set.symdef
{OPTION XPROFILE}
for acc = start, prgele ∈ p do
 if isempty.code.prgele then
  prgele ∪ acc
 else
  firstopt:T(librarymap, acc, prgele, false, typedict, libname) ∪ acc
/do acc

function firstopt:T(librarymap:seq.word
 , p:set.symdef
 , sd:symdef
 , first:boolean
 , typedict:typedict
 , libname:word) symdef
let s = sym.sd
let pdict = 
 for pmap = empty:set.localmap2, parano ∈ arithseq(nopara.s, 1, 1) do
  pmap + localmap2(parano, [Local.parano])
 /do pmap
let a = xxx:T(librarymap, p, code.sd, s, pdict, typedict, libname)
let t = 
 if first then
  a
 else if Hasfor ∈ flags.a ∨ Callself ∈ flags.a then
  let ty = if Hasfor ∈ flags.a then expandIndex(code.a, nextvar.a) else a
  let t2 = if Callself ∈ flags.a then mergeblocks(code.ty, s) else code.ty,
  expandresult(nextvar.ty, t2, flags.a)
 else
  a
let options = getOptions.sd
let newoptions1 = 
 if between(length.code.t, 1, 21) ∧ Callself ∉ flags.t ∧ Hasfor ∉ flags.t
 ∧ not.isNOINLINE.sd then
  if isverysimple(nopara.s, code.t) then "INLINE VERYSIMPLE" else "INLINE"
 else
  ""
let newoptions = 
 if isempty.options then
  newoptions1
 else if options = newoptions1 then
  options
 else
  toseq(asset.options \ asset."VERYSIMPLE" ∪ asset.newoptions1)
,
symdef4(sym.sd, code.t, paragraphno.sd, newoptions)

function xxx:T(librarymap:seq.word
 , p:set.symdef
 , code:seq.symbol
 , s:symbol
 , pdict:set.localmap2
 , typedict:typedict
 , libname:word) expandresult
let a = scancode:T(librarymap, p, code, nopara.s + 1, pdict, s, typedict, libname)
let new = if Hasmerge ∈ flags.a then mergeblocks(code.a, Lit.1) else code.a,
if length.code = length.new ∧ length.code > 20 ∨ new = code then
 expandresult(nextvar.a, new, flags.a)
else
 xxx:T(librarymap, p, new, s, pdict, typedict, libname)

function scancode:T(librarymap:seq.word
 , p:set.symdef
 , org:seq.symbol
 , nextvarX:int
 , mapX:set.localmap2
 , self:symbol
 , typedict:typedict
 , libname:word) expandresult
for flags = bits.0
 , result = empty:seq.symbol
 , nextvar = nextvarX
 , map = mapX
 , sym ∈ org
do
 let len = length.result,
 if isconst.sym then
  next(flags, result + sym, nextvar, map)
 else if isspecial.sym then
  if isdefine.sym then
   let thelocal = value.sym,
   if len > 0 ∧ (isconst.result_len ∨ islocal.result_len) then
    next(flags
     , subseq(result, 1, length.result - 1)
     , nextvar
     , localmap2(thelocal, [result_len]) ∪ map)
   else
    next(flags
     , result + Define.nextvar
     , nextvar + 1
     , localmap2(thelocal, [Local.nextvar]) ∪ map)
  else
   {if isbr.sym then let newsym = sym next (if brt.newsym = brf.newsym ∨ isblock.last.result1 then Hasmerge
    ∨ flags else flags, result+newsym, nextvar, map) else}
   if isExit.sym ∧ isblock.last.result ∨ isbr.sym ∧ isconst.last.result then
    next(flags ∨ Hasmerge, result + sym, nextvar, map)
   else if isloopblock.sym then
    let nopara = nopara.sym
    let addlooplocals = 
     for pmap = map, parano = 1, e ∈ constantseq(10000, 1)
     while parano ≤ nopara
     do
      next(localmap2(firstvar.sym + parano - 1, [Local(nextvar + parano - 1)]) ∪ pmap
       , parano + 1)
     /do pmap
    ,
    next(flags
     , result + Loopblock(paratypes.sym, nextvar, resulttype.sym)
     , nextvar + nopara
     , addlooplocals)
   else if isRecord.sym ∨ isSequence.sym then
    let nopara = nopara.sym
    let args = subseq(result, len + 1 - nopara, len)
    let constargs = for acc = true, @e ∈ args while acc do isconst.@e /do acc,
    if constargs then
     next(flags
      , subseq(result, 1, len - nopara) + Constant2(libname, args + sym)
      , nextvar
      , map)
    else
     next(flags, result + sym, nextvar, map)
   else if islocal.sym then
    let t = lookup(map, value.sym),
    next(flags, result + if isempty.t then [sym] else value.t_1, nextvar, map)
   else
    next(flags, result + sym, nextvar, map)
 else if sym = NotOp ∧ last.result = NotOp then
  next(flags, result >> 1, nextvar, map)
 else if length.result > 2 ∧ isconst.last.result ∧ ismember.sym then
  let arg = result_(length.result - 1)
  let nonew = islocal.arg ∨ isconst.arg
  let z = seqelements.last.result
  let var = if nonew then arg else Local.nextvar
  let newcode = 
   if isempty.z then
    [Litfalse]
   else if length.z = 1 then
    [var, first.z, EqOp]
   else
    let t = length.z + 2,
    for acc = [Start.typeboolean], idx = 2, w ∈ z >> 1 do
     next(acc + [var, w, EqOp] + Br2(t - idx, 1), idx + 1)
    /do acc + [var, last.z, EqOp, Exit, Littrue, Exit, EndBlock]
  ,
  if nonew then
   next(flags, result >> 2 + newcode, nextvar, map)
  else
   next(flags, result >> 1 + Define.nextvar + newcode, nextvar + 1, map)
 else if name.sym ∈ "checkfornoop" ∧ module.sym = internalmod then
  let noop = forexpisnoop(self, result),
  if not.isempty.noop then
   next(flags, noop, nextvar, map)
  else
   next(flags ∨ Hasfor, result + sym, nextvar, map)
 else if wordname.sym ∈ "indexseq45 idxNB" ∧ isInternal.sym then
  next(flags ∨ Hasfor, result + sym, nextvar, map)
 else if sym = self then
  next(flags ∨ Callself, result + sym, nextvar, map)
 else if isInternal.sym ∧ name.sym ∈ "getseqlength" ∧ isconst.last.result then
  if iswords.last.result then
   next(flags, result >> 1 + Lit.length.worddata.last.result, nextvar, map)
  else
   let x = last.fullconstantcode.last.result,
   if isSequence.x then
    next(flags, result >> 1 + Lit.nopara.x, nextvar, map)
   else
    next(flags, result + sym, nextvar, map)
 else
  let nopara = nopara.sym
  let b = getSymdef(p, sym)
  let options = if isempty.b then "" else getOptions.b_1
  let compiletime = 
   if first."COMPILETIME" ∉ options ∧ (name.sym ∉ "_" ∨ nopara ≠ 2) then
    empty:seq.symbol
   else
    let args = subseq(result, len - nopara + 1, len),
    interpretCompileTime:T(librarymap, subseq(result, len - nopara + 1, len), sym, typedict)
  ,
  if not.isempty.compiletime then
   let newconst = if length.compiletime > 1 then Constant2(libname, compiletime) else first.compiletime,
   next(flags, result >> nopara + newconst, nextvar, map)
  else
   let newresult = checkemptycat:T(sym, result),
   if not.isempty.newresult then
    next(flags, newresult, nextvar, map)
   else
    let code = if isempty.b then empty:seq.symbol else code.b_1,
    if first."VERYSIMPLE" ∈ options then
     next(flags, result + code << nopara.sym, nextvar, map)
    else if "INLINE"_1 ∉ options then
     let newflags = if "STATE"_1 ∈ options ∨ isGlobal.sym then State ∨ flags else flags,
     next(newflags, result + sym, nextvar, map)
    else if isempty.code then
     next(flags, result + sym, nextvar, map)
    else if length.code = 1 ∧ code = [Local.1] ∧ nopara = 1 then
     {function just returns result} next(flags, result, nextvar, map)
    else
     let t = backparse2(result, len, nopara, empty:seq.int) + [len + 1]
     let new = expandinline:T(librarymap, result, t, nextvar, code, p, self, typedict, libname),
     next(flags ∨ flags.new, subseq(result, 1, t_1 - 1) + code.new, nextvar.new, map)
/do expandresult(nextvar, result, flags)

function checkemptycat:T(sym:symbol, result:seq.symbol) seq.symbol
if name.sym ∈ "+" ∧ paratypes.sym = [seqof.typeword, seqof.typeword] then
 if last.result = Words."" then
  result >> 1
 else
  let t = backparse2(result, length.result, 2, empty:seq.int),
  if subseq(result, t_1, t_2 - 1) = [Words.""] then
   subseq(result, 1, t_1 - 1) + subseq(result, t_2, length.result)
  else
   empty:seq.symbol
else
 empty:seq.symbol

function expandinline:T(librarymap:seq.word
 , result:seq.symbol
 , t:seq.int
 , nextvarin:int
 , code:seq.symbol
 , p:set.symdef
 , self:symbol
 , typedict:typedict
 , libname:word) expandresult
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
  , idx)
/do
 let r = scancode:T(librarymap, p, code, nextvar, pmap, self, typedict, libname),
 expandresult(nextvar.r, paracode + code.r, flags.r) 