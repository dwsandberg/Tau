Module compilerfrontT.T

use compileTimeT.T

use addprofile

use backparse

use compilerfront

use entrypoint

use file

use seq.file

use localmap2

use set.localmap2

use objectio.midpoint

use seq.midpoint

use seq.modExports

use seq.mytype

use seq.seq.mytype

use pass2

use standard

use stack.stkele

use symbol

use seq.symbol

use otherseq.seq.symbol

use symbol2

use symbolconstant

use seq.symdef

use set.symdef

use set.word

Function newanal:T(
ss:seq.symbol
, self:symbol
, final:boolean
, nojumptable:boolean
) seq.symbol
let nopara = nopara.self
for pdict = empty:set.localmap2, parano ∈ arithseq(nopara, 1, 1)
do pdict + localmap2(parano, [Local.parano]),
code.newanal:T(
 ""
 , empty:set.symdef
 , ss
 , self
 , nopara + 1
 , pdict
 , 1#"dummylib"
 , emptytypedict
 , final
 , nojumptable
)

Function compilerFront:T(
option:seq.word
, input:seq.file
, exports0:seq.word
, entryUses:seq.word
) midpoint
{OPTION PROFILE}
for libinfo = empty:midpoint, srcfiles = empty:seq.file, i ∈ input
do
 if ext.fn.i ∈ "libinfo" then
  let new = 1#inbytes:midpoint(data.i),
  next(
   midpoint(
    ""
    , prg.libinfo ∪ prg.new
    , emptytypedict
    , libmods.libinfo + libmods.new
    , empty:seq.seq.word
   )
   , srcfiles
  )
 else if ext.fn.i ∈ "lib html" then next(libinfo, srcfiles)
 else
  assert ext.fn.i ∈ "ls libsrc" report "Extension" + fullname.fn.i,
  next(libinfo, srcfiles + i)
let allsrc = breakparagraph.srcfiles
let libname = libname.midpoint(option, empty:set.symdef, emptytypedict, empty:seq.modExports, allsrc)
let exports = extractExports(allsrc, exports0)
let m =
 if 1#"bitcode" ∉ option then compilerfront3(option, allsrc, libname, exports, libinfo)
 else
  let EPname = merge.[libname, 1#"$EP"],
  compilerfront3(
   option
   , allsrc + ["Module^(EPname)"] + modEntry(allsrc, entryUses, false)
   , libname
   , exports + EPname
   , libinfo
  ),
if 1#option.m ∈ "library text pass1 pass1a prebind" then m
else
 let librarymap = [libname, 1#"*"]
 let prg = {if" xxx"#1 ∈ option then GG.hasstate.prg.m else} prg.m
 let prg5 = pass2:T(librarymap, prg, typedict.m, option, libname),
 let m2 =
  if 1#"profile" ∈ option then
   let profinit = symbol(moduleref.[libname, 1#"initialize"], "initProfile", typeptr)
   let profdata = symbol(moduleref.[libname, 1#"initialize"], "profileData", typeptr),
   let prg6 = addprofile(prg5, libname),
   if isempty.prg6 then m
   else
    midpoint5(
     option
     , prg6 ∪ prg5
     , templates.m
     , typedict.m
     , libmods.m + modExports(module.profinit, [profinit, profdata], empty:seq.seq.mytype)
     , src.m
    )
  else midpoint5(option, prg5, templates.m, typedict.m, libmods.m, src.m),
 if 1#"bitcode" ∈ option then
  let m3 = prepareback(m2, libinfo, extractValue(option, "uses")),
  midpoint5(option.m3, prg.m3, templates.m3, typedict.m3, libmods.m3, src.m3 + allsrc)
 else midpoint5(option.m2, prg.m2, templates.m2, typedict.m2, libmods.m2, src.m2 + allsrc)

/use otherseq.seq.word

/use otherseq.word

unbound interpretCompileTime:T(
librarymap:seq.word
, args:seq.symbol
, ctsym:symbol
, typedict:typedict
) seq.symbol

Function pass2:T(
librarymap:seq.word
, prg:set.symdef
, typedict:typedict
, option:seq.word
, libname:word
) set.symdef
{OPTION PROFILE}
let nojumptable = 1#"nojumptable" ∈ option
for big = empty:seq.symdef, core = empty:seq.symdef, pele0 ∈ toseq.prg
do
 if isempty.code.pele0 then next(big, core + pele0)
 else
  let code = code.pele0
  for acc = [1#code], last = 1#code, c ∈ code << 1
  do next(if last = PreFref then acc >> 1 + Fref.c else acc + c, c),
  let sd = symdef4(sym.pele0, acc, paragraphno.pele0, getOptions.pele0),
  if isrecordconstant.sym.sd then
   let discard = registerConstant.sd,
   next(big, core)
  else if n.code < 35 then next(big, core + sd)
  else next(big + sd, core)
for c2 = empty:set.symdef, pele ∈ core
do c2 + firstopt:T(librarymap, c2, pele, typedict, libname, nojumptable)
for c3 = c2, pele ∈ toseq.c2
do firstopt:T(librarymap, c3, pele, typedict, libname, nojumptable) ∪ c3
for c4 = c3, pele ∈ big
do firstopt:T(librarymap, c4, pele, typedict, libname, nojumptable) ∪ c4,
c4 ∪ constantsymbols.libname

function firstopt:T(
librarymap:seq.word
, p:set.symdef
, sd:symdef
, typedict:typedict
, libname:word
, nojumptable:boolean
) symdef
{OPTION XPROFILE}
let self = sym.sd
let nopara = nopara.self
for pdict = empty:set.localmap2, parano ∈ arithseq(nopara, 1, 1)
do pdict + localmap2(parano, [Local.parano])
for code1 = code.sd, last ∈ [false, false, true]
do
 code.newanal:T(librarymap, p, code1, self, nopara + 1, pdict, libname, typedict, last, nojumptable)
let options = getOptions.sd
let newoptions1 =
 if between(n.code1, 1, 25) ∧ not.isNOINLINE.sd ∧ self ∉ code1 then if isverysimple(nopara, code1) then "INLINE VERYSIMPLE" else "INLINE"
 else ""
let newoptions =
 if isempty.options then newoptions1
 else if options = newoptions1 then options
 else toseq(asset.options \ asset."VERYSIMPLE" ∪ asset.newoptions1),
symdef4(self, code1, paragraphno.sd, newoptions)

Function newanal:T(
librarymap:seq.word
, prg:set.symdef
, ss:seq.symbol
, self:symbol
, nextvarX:int
, mapX:set.localmap2
, libname:word
, typedict:typedict
, final:boolean
, nojumptable:boolean
) expandresult
{OPTION XPROFILE}
let renumber = true
let EndMark = symbol(internalmod, "endmark", typeint)
for
 injump = false
 , part = empty:seq.symbol
 , blkparts = empty:seq.seq.symbol
 , stk = empty:stack.stkele
 , nextvar = nextvarX
 , map = mapX
 , sym = Lit.0
 , ahead ∈ ss + (if isconst.self then Lit.0 else EndMark)
do
 if injump then
  if isJmp.sym then next(false, empty:seq.symbol, blkparts + (part + sym), stk, nextvar, map, ahead)
  else next(injump, part + sym, blkparts, stk, nextvar, map, ahead)
 else if not.isspecial.sym then
  if isconst.sym then next(injump, part + sym, blkparts, stk, nextvar, map, ahead)
  else if sym = NotOp then
   let last = 1^part
   let newPart =
    if last = NotOp then part >> 1
    else if last = Littrue then part >> 1 + Litfalse
    else if last = Litfalse then part >> 1 + Littrue
    else part + sym,
   next(injump, newPart, blkparts, stk, nextvar, map, ahead)
  else if n.part ≥ 2 ∧ isconst.1^part ∧ ismember.sym then
   let arg = 2^part
   let nonew = islocal.arg ∨ isconst.arg,
   next(
    injump
    , isMemberCode(part, arg, nextvar, nonew)
    , blkparts
    , stk
    , if nonew then nextvar else nextvar + 1
    , map
    , ahead
   )
  else if sym = self then next(injump, part + sym, blkparts, stk, nextvar, map, ahead)
  else
   let newresult = checkemptycat(sym, part),
   if not.isempty.newresult then next(injump, newresult, blkparts, stk, nextvar, map, ahead)
   else
    let nopara = nopara.sym
    let b = getSymdef(prg, sym)
    let options = if isempty.b then "" else getOptions.1#b,
    let compiletime =
     if not(1#"COMPILETIME" ∈ options ∨ name.sym ∈ "#idxNB" ∧ nopara = 2) then empty:seq.symbol
     else
      let len = n.part
      let args = subseq(part, len - nopara + 1, len),
      for allconstant = true, sy ∈ args while allconstant do isconst.sy,
      if allconstant then {let discard100 = track.sym} interpretCompileTime:T(librarymap, args, sym, typedict)
      else empty:seq.symbol,
    if not.isempty.compiletime then
     let newconst = if n.compiletime > 1 then Constant2(libname, compiletime) else 1#compiletime,
     next(injump, part >> nopara + newconst, blkparts, stk, nextvar, map, ahead)
    else if wordname.sym ∈ "idxNB" ∧ isInternal.sym then
     if final then
      let tmp = expandIdxNB(part, sym, nextvar, typedict),
      next(injump, code.tmp, blkparts, stk, nextvar.tmp, map, ahead)
     else next(injump, part + sym, blkparts, stk, nextvar, map, ahead)
    else
     let code = if isempty.b then empty:seq.symbol else code.1#b,
     if 1#"VERYSIMPLE" ∈ options ∧ not.final then next(injump, part + code << nopara.sym, blkparts, stk, nextvar, map, ahead)
     else if n.code = 1 ∧ code = [Local.1] ∧ nopara = 1 then {function just returns result} next(injump, part, blkparts, stk, nextvar, map, ahead)
     else if 1#"INLINE" ∉ options ∨ isempty.code ∨ final then next(injump, part + sym, blkparts, stk, nextvar, map, ahead)
     else if nopara = 0 then
      let r =
       newanal:T(
        librarymap
        , prg
        , code
        , self
        , nextvar
        , empty:set.localmap2
        , libname
        , typedict
        , final
        , nojumptable
       ),
      next(injump, part + code.r, blkparts, stk, nextvar.r, map, ahead)
     else if name.sym ∈ "+"
     ∧ %.sym ∈ [{???? should be needed} "seq.word:+(seq.word, seq.word) seq.word"] then next(injump, part + sym, blkparts, stk, nextvar, map, ahead)
     else
      for
       paracode = empty:seq.symbol
       , pmap = empty:set.localmap2
       , nextvarExpand = nextvar
       , idx = n.part
       , parano = nopara
      while parano > 1
      do
       let tmp = backparse3(part, idx, true),
       next(
        {paracode} subseq(part, tmp, idx) + Define.nextvarExpand + paracode
        , pmap + localmap2(parano, [Local.nextvarExpand])
        , nextvarExpand + 1
        , {idx} tmp - 1
        , parano - 1
       )
      let r =
       newanal:T(
        librarymap
        , prg
        , code
        , self
        , nextvarExpand + 1
        , pmap + localmap2(1, [Local.nextvarExpand])
        , libname
        , typedict
        , final
        , nojumptable
       ),
      let expandresult = subseq(part, 1, idx) + Define.nextvarExpand + paracode + code.r,
      next(injump, expandresult, blkparts, stk, nextvar.r, map, ahead)
 else
  {isspecial.sym is true}
  if islocal.sym then
   let t = lookup(map, value.sym),
   next(
    injump
    , part + (if isempty.t then [sym] else value.1#t)
    , blkparts
    , stk
    , nextvar
    , map
    , ahead
   )
  else if isdefine.sym then
   let thelocal = value.sym
   let len = n.part,
   if len > 0 ∧ (isconst.len#part ∨ islocal.len#part) then next(injump, part >> 1, blkparts, stk, nextvar, localmap2(thelocal, [len#part]) ∪ map, ahead)
   else if renumber then
    next(
     injump
     , part + Define.nextvar
     , blkparts
     , stk
     , nextvar + 1
     , localmap2(thelocal, [Local.nextvar]) ∪ map
     , ahead
    )
   else next(injump, part + sym, blkparts, stk, nextvar, map, ahead)
  else if isRecord.sym ∨ isSequence.sym then
   let nopara = nopara.sym
   let len = n.part
   let args = subseq(part, len + 1 - nopara, len),
   for constargs = n.args = nopara, @e ∈ args
   while constargs
   do isconst.@e,
   if constargs then
    next(
     injump
     , part >> nopara + Constant2(libname, args + sym)
     , blkparts
     , stk
     , nextvar
     , map
     , ahead
    )
   else next(injump, part + sym, blkparts, stk, nextvar, map, ahead)
  else if iscontinue.sym ∨ isExit.sym then next(injump, empty:seq.symbol, blkparts + (part + sym), stk, nextvar, map, ahead)
  else if isJmp.sym then next(true, part + sym, blkparts, stk, nextvar, map, ahead)
  else if isloopblock.sym ∧ renumber then
   let nopara = nopara.sym
   let addlooplocals =
    for pmap = map, parano = 1, e ∈ constantseq(10000, 1)
    while parano ≤ nopara
    do
     next(
      localmap2(firstvar.sym + parano - 1, [Local(nextvar + parano - 1)]) ∪ pmap
      , parano + 1
     ),
    pmap,
   let newsym = Loopblock(paratypes.sym, nextvar, resulttype.sym),
   next(
    injump
    , empty:seq.symbol
    , empty:seq.seq.symbol
    , push(stk, stkele(part + newsym, blkparts))
    , nextvar + nopara
    , addlooplocals
    , ahead
   )
  else if isstartorloop.sym then
   next(
    injump
    , empty:seq.symbol
    , empty:seq.seq.symbol
    , push(stk, stkele(part + sym, blkparts))
    , nextvar
    , map
    , ahead
   )
  else if isbr.sym then
   let newpart =
    if 1^part = NotOp then part >> 1 + Br2(brf.sym, brt.sym)
    else part + Br2(brt.sym, brf.sym),
   next(injump, empty:seq.symbol, blkparts + newpart, stk, nextvar, map, ahead)
  else if sym = EndBlock then
   let blockheader = 1^part.top.stk
   let nonLoop = isstart.blockheader,
   let checkNoOp =
    if not.nonLoop ∧ nopara.blockheader = 2 then checkLoopIsNoOp(part.top.stk, blkparts, self)
    else empty:seq.symbol,
   if not.isempty.checkNoOp then next(injump, checkNoOp, blkparts.top.stk, pop.stk, nextvar, map, ahead)
   else if 1^(1#blkparts) = Exit ∧ nonLoop then
    {remove block with just one Exit}
    next(
     injump
     , part.top.stk >> 1 + 1#blkparts >> 1
     , blkparts.top.stk
     , pop.stk
     , nextvar
     , map
     , ahead
    )
   else if ahead = Exit ∧ nonLoop then
    {combine current block with outer block}
    let tmp2 = adjustbr(blkparts.top.stk, n.blkparts) + [part.top.stk >> 1 + 1#blkparts] + blkparts << 1,
    next(injump, 1^tmp2 >> 1, tmp2 >> 1, pop.stk, nextvar, map, 1^(1^tmp2))
   else if isbr.ahead ∧ nonLoop then
    {combine boolean block with outer block}
    for partsA = empty:seq.seq.symbol, brt = brt.ahead, brf = brf.ahead, p ∈ reverse.blkparts
    do
     let p1 = if 1^p = Exit then p >> 1 + Br2(brt, brf) else p,
     next([p1] + partsA, brt + 1, brf + 1)
    let tmp2 = adjustbr(blkparts.top.stk, n.blkparts) + [part.top.stk >> 1 + 1#partsA] + partsA << 1,
    next(injump, 1^tmp2 >> 1, tmp2 >> 1, pop.stk, nextvar, map, 1^(1^tmp2))
   else
    let recursive =
     if final ∧ nonLoop ∧ ahead = EndMark then checkrecursive(blkparts, self, part.top.stk, nojumptable)
     else empty:seq.symbol,
    if not.isempty.recursive then next(injump, recursive, blkparts.top.stk, pop.stk, nextvar + nopara.self, map, ahead)
    else
     next(
      injump
      , blocktocode(part.top.stk, blkparts, self, nojumptable)
      , blkparts.top.stk
      , pop.stk
      , nextvar
      , map
      , ahead
     )
  else next(injump, part + sym, blkparts, stk, nextvar, map, ahead)
{for maxvar = nextvarX-1, p ∈ part do if islocal.p ∨ isdefine.p then max (value.p, maxvar) else maxvar assert maxvar < nextvar report %.maxvar+"
/br nextvar^(nextvar)
/br self:^(self)"+%.part,}
expandresult(nextvar, part << 1) 