Module compilerfrontT.T

use compileTimeT.T

use addprofile

use backparse

use bits

use seq.byte

use compilerfront

use file

use otherseq.int

use seq.int

use localmap2

use set.localmap2

use makeentry

use objectio.midpoint

use seq.midpoint

use seq.modExports

use seq.mytype

use seq.seq.mytype

use newanal

use pass2

use standard

use symbol

use seq.symbol

use set.symbol

use symbol2

use symbolconstant

use seq.symdef

use set.symdef

use textio

use seq.seq.word

use set.word

Function compilerFront:T(option:seq.word, input:seq.file) midpoint
compilerFront:T(option, input, "", "", "")

Function compilerFront:T(
 option:seq.word
 , input:seq.file
 , libname0:seq.word
 , exports0:seq.word
) midpoint
compilerFront:T(option, input, libname0, exports0, "")

Function compilerFront:T(
 option:seq.word
 , input:seq.file
 , libname0:seq.word
 , exports0:seq.word
 , entryUses:seq.word
) midpoint
{OPTION XPROFILE}
for libinfo = empty:midpoint, data = empty:seq.byte, i ∈ input
do
 if ext.fn.i ∈ "libinfo" then
  let new = 1_inbytes:midpoint(data.i),
  next(
   midpoint("", prg.libinfo ∪ prg.new, emptytypedict, libmods.libinfo + libmods.new, empty:seq.seq.word)
   , data
  )
 else if ext.fn.i ∈ "lib html" then
 next(libinfo, data)
 else
  assert ext.fn.i ∈ "ls libsrc" report "Extension" + fullname.fn.i,
  next(libinfo, data + [tobyte.10, tobyte.10] + data.i)
let allsrc = breakparagraph.data
let libname =
 if isempty.libname0 then
  let lib0 = extractValue(1_allsrc, "Library")
  assert not.isempty.lib0 report "no library specified",
  1_lib0
 else 1_libname0
let exports = extractExports(allsrc, exports0)
let m =
 if 1_"bitcode" ∉ option then
 compilerfront3(option, allsrc, libname, exports, libinfo)
 else
  let EPname = merge.[libname, 1_"$EP"],
  compilerfront3(
   option
   , allsrc + ["Module^(EPname)"] + modEntry(allsrc, entryUses)
   , libname
   , exports + EPname
   , libinfo
  ),
if 1_option.m ∈ "library text pass1 pass1a prebind" then
m
else
 let librarymap = [libname, 1_"*"]
 let prg = {if" xxx"_1 ∈ option then GG.hasstate.prg.m else} prg.m
 let prg5 = pass2:T(librarymap, prg, typedict.m, option, libname)
 {assert false report trackresults}
 let m2 =
  if 1_"profile" ∈ option then
   let profinit = symbol(moduleref.[libname, 1_"initialize"], "initProfile", typeptr)
   let profdata = symbol(moduleref.[libname, 1_"initialize"], "profileData", typeptr)
   let prg6 = addprofile(prg5, libname),
    if isempty.prg6 then
    m
    else midpoint5(
     option
     , prg6 ∪ prg5
     , templates.m
     , typedict.m
     , libmods.m + modExports(module.profinit, [profinit, profdata], empty:seq.seq.mytype)
     , src.m
    )
  else midpoint5(option, prg5, templates.m, typedict.m, libmods.m, src.m),
  if 1_"bitcode" ∈ option then
   let m3 = prepareback(m2, libinfo),
   midpoint5(option.m3, prg.m3, templates.m3, typedict.m3, libmods.m3, src.m3 + allsrc)
  else m2

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
 , t:typedict
 , option:seq.word
 , libname:word
) set.symdef
{OPTION XPROFILE}
{for idxNBsyms = empty:seq.symdef, tp ∈ packedtypes+typeint+typereal+typeboolean+
 typeptr+typebyte do idxNBsyms+symdef4 (symbol (internalmod," idxNB", seqof.tp, typeint
 , tp), empty:seq.symbol, 0," COMPILETIME")}
for knownsymbols = empty:set.symdef, pele0 ∈ toseq.prg
do
 if isempty.code.pele0 then
 knownsymbols + pele0
 else
  let code = code.pele0
  for acc = [1_code], last = 1_code, c ∈ code << 1
  do next(if last = PreFref then acc >> 1 + Fref.c else acc + c, c)
  let sd = symdef4(sym.pele0, acc, paragraphno.pele0, getOptions.pele0),
   if isrecordconstant.sym.sd then
   let discard = registerConstant.sd, knownsymbols
   else knownsymbols + sd,
if 1_"addpass" ∈ option then
additionalpass:T(librarymap, toseq.knownsymbols, knownsymbols, t, libname)
else
 subpass2:T(librarymap, empty:seq.symdef, empty:set.symdef, knownsymbols, 0, t, libname)
 ∪ constantsymbols.libname

function subpass2:T(
 librarymap:seq.word
 , bigin:seq.symdef
 , corein:set.symdef
 , toprocess:set.symdef
 , count:int
 , typedict:typedict
 , libname:word
) set.symdef
{OPTION XPROFILE}
for big = bigin, small = empty:set.symdef, core = corein, pele ∈ toseq.toprocess
do
 let s = sym.pele
 let code = code.pele,
  if isempty.code ∨ isVERYSIMPLE.pele ∨ isINLINE.pele then
  next(big, small, pele ∪ core)
  else if isCOMPILETIME.pele then
  next(big, small, firstopt:T(librarymap, core, pele, true, typedict, libname) ∪ core)
  else if n.code < 30 then
   let t = firstopt:T(librarymap, core, pele, true, typedict, libname),
   if isINLINE.t then next(big, small, t ∪ core) else next(big, t ∪ small, core)
  else next(big + pele, small, core),
if n.toseq.corein = n.toseq.core then
additionalpass:T(librarymap, toseq.core + toseq.small + big, core, typedict, libname)
else subpass2:T(librarymap, big, core, small, count + 1, typedict, libname)

Function additionalpass:T(
 librarymap:seq.word
 , p:seq.symdef
 , start:set.symdef
 , typedict:typedict
 , libname:word
) set.symdef
{OPTION XPROFILE}
for acc = start, prgele ∈ p
do
 if isempty.code.prgele then
 prgele ∪ acc
 else firstopt:T(librarymap, acc, prgele, false, typedict, libname) ∪ acc,
acc

function firstopt:T(
 librarymap:seq.word
 , p:set.symdef
 , sd:symdef
 , first:boolean
 , typedict:typedict
 , libname:word
) symdef
{OPTION PROFILE}
let self = sym.sd
let nopara = nopara.self
for pdict = empty:set.localmap2, parano ∈ arithseq(nopara, 1, 1)
do pdict + localmap2(parano, [Local.parano])
let a0 = scancode:T(librarymap, p, code.sd, nopara + 1, pdict, self, typedict, libname, true)
let code3 = newanal(code.a0, Lit.0)
let a1 = scancode:T(librarymap, p, code3, nopara + 1, pdict, self, typedict, libname, true)
let code4 = newanal(code.a1, self)
let a2 = scancode:T(librarymap, p, code4, nopara + 1, pdict, self, typedict, libname, true)
let flags = flags.a2
let nextvar = nextvar.a2
let code = code.a2
let code1 = if HasidxNB ∈ flags then code.expandIndex(code, nextvar, typedict) else code
let options = getOptions.sd
let newoptions1 =
 if between(n.code1, 1, 25) ∧ not.isNOINLINE.sd ∧ self ∉ code1 then
 if isverysimple(nopara, code1) then "INLINE VERYSIMPLE" else "INLINE"
 else ""
let newoptions =
 if isempty.options then
 newoptions1
 else if options = newoptions1 then
 options
 else toseq(asset.options \ asset."VERYSIMPLE" ∪ asset.newoptions1),
symdef4(self, code1, paragraphno.sd, newoptions)

function scancode:T(
 librarymap:seq.word
 , p:set.symdef
 , org:seq.symbol
 , nextvarX:int
 , mapX:set.localmap2
 , self:symbol
 , typedict:typedict
 , libname:word
 , renumber:boolean
) expandresult
for flags = bits.0, result = empty:seq.symbol, nextvar = nextvarX, map = mapX, sym ∈ org
do
 let len = n.result,
  if isconst.sym then
  next(flags, result + sym, nextvar, map)
  else if isspecial.sym then
   if islocal.sym then
    let t = lookup(map, value.sym),
    next(flags, result + if isempty.t then [sym] else value.1_t, nextvar, map)
   else if isdefine.sym then
    let thelocal = value.sym,
     if len > 0 ∧ (isconst.len_result ∨ islocal.len_result) then
     next(flags, subseq(result, 1, n.result - 1), nextvar, localmap2(thelocal, [len_result]) ∪ map)
     else if renumber then
     next(flags, result + Define.nextvar, nextvar + 1, localmap2(thelocal, [Local.nextvar]) ∪ map)
     else next(flags, result + sym, nextvar, map)
   else if isloopblock.sym ∧ renumber then
    let nopara = nopara.sym
    let addlooplocals =
     for pmap = map, parano = 1, e ∈ constantseq(10000, 1)
     while parano ≤ nopara
     do next(
      localmap2(firstvar.sym + parano - 1, [Local(nextvar + parano - 1)]) ∪ pmap
      , parano + 1
     ),
     pmap,
    next(
     flags
     , result + Loopblock(paratypes.sym, nextvar, resulttype.sym)
     , nextvar + nopara
     , addlooplocals
    )
   else if isRecord.sym ∨ isSequence.sym then
    let nopara = nopara.sym
    let args = subseq(result, len + 1 - nopara, len)
    let constargs = for acc = true, @e ∈ args while acc do isconst.@e, acc,
     if constargs then
     next(flags, subseq(result, 1, len - nopara) + Constant2(libname, args + sym), nextvar, map)
     else next(flags, result + sym, nextvar, map)
   else next(flags, result + sym, nextvar, map)
  else if sym = NotOp then
   let last = 1^result,
    if last = NotOp then
    next(flags, result >> 1, nextvar, map)
    else if last = Littrue then
    next(flags, result >> 1 + Litfalse, nextvar, map)
    else if last = Litfalse then
    next(flags, result >> 1 + Littrue, nextvar, map)
    else next(flags, result + sym, nextvar, map)
  else if n.result > 2 ∧ isconst.1^result ∧ ismember.sym then
   let arg = (n.result - 1)_result
   let nonew = islocal.arg ∨ isconst.arg
   let z = seqelements.1^result
   let var = if nonew then arg else Local.nextvar
   let newcode =
    if isempty.z then
    [Litfalse]
    else if n.z = 1 then
    [var, 1_z, EqOp]
    else
     let t = n.z + 2
     for acc = [Start.typeboolean], idx = 2, w ∈ z >> 1
     do next(acc + [var, w, EqOp] + Br2(t - idx, 1), idx + 1),
     acc + [var, 1^z, EqOp, Exit, Littrue, Exit, EndBlock],
    if nonew then
    next(flags, result >> 2 + newcode, nextvar, map)
    else next(flags, result >> 1 + Define.nextvar + newcode, nextvar + 1, map)
  else if sym = self then
  next(flags ∨ Callself, result + sym, nextvar, map)
  else
   {assert name.sym /nin" idxNB" report" jkl^(sym)"}
   let nopara = nopara.sym
   let b = getSymdef(p, sym)
   let options = if isempty.b then "" else getOptions.1_b
   let compiletime =
    if not(1_"COMPILETIME" ∈ options ∨ name.sym ∈ "_idxNB" ∧ nopara = 2) then
    empty:seq.symbol
    else
     let args = subseq(result, len - nopara + 1, len)
     for allconstant = true, sy ∈ args while allconstant do isconst.sy,
      if allconstant then
      {let discard100 = track.sym} interpretCompileTime:T(librarymap, args, sym, typedict)
      else empty:seq.symbol,
    if not.isempty.compiletime then
     let newconst = if n.compiletime > 1 then Constant2(libname, compiletime) else 1_compiletime,
     next(flags, result >> nopara + newconst, nextvar, map)
    else if wordname.sym ∈ "idxNB" ∧ isInternal.sym then
    next(flags ∨ HasidxNB, result + sym, nextvar, map)
    else
     let newresult = checkemptycat(sym, result),
      if not.isempty.newresult then
      next(flags, newresult, nextvar, map)
      else
       let code = if isempty.b then empty:seq.symbol else code.1_b,
        if 1_"VERYSIMPLE" ∈ options then
        next(flags, result + code << nopara.sym, nextvar, map)
        else if 1_"INLINE" ∉ options then
         let newflags = if 1_"STATE" ∈ options ∨ isGlobal.sym then State ∨ flags else flags,
         next(newflags, result + sym, nextvar, map)
        else if isempty.code then
        next(flags, result + sym, nextvar, map)
        else if n.code = 1 ∧ code = [Local.1] ∧ nopara = 1 then
        {function just returns result} next(flags, result, nextvar, map)
        else if nopara = 0 then
         let r = scancode:T(librarymap, p, code, nextvar, empty:set.localmap2, self, typedict, libname, true),
         next(flags ∨ flags.r, result + code.r, nextvar.r, map)
        else
         for
          paracode = empty:seq.symbol
          , pmap = empty:set.localmap2
          , nextvarExpand = nextvar
          , idx = len
          , parano = nopara
         while parano > 1
         do
          let tmp = backparse3(result, idx, true),
          next(
           {paracode} subseq(result, tmp, idx) + Define.nextvarExpand + paracode
           , pmap + localmap2(parano, [Local.nextvarExpand])
           , nextvarExpand + 1
           , {idx} tmp - 1
           , parano - 1
          )
         let r = scancode:T(
          librarymap
          , p
          , code
          , nextvarExpand + 1
          , pmap + localmap2(1, [Local.nextvarExpand])
          , self
          , typedict
          , libname
          , true
         )
         let expandresult = subseq(result, 1, idx) + Define.nextvarExpand + paracode + code.r,
         next(flags ∨ flags.r, expandresult, nextvar.r, map),
expandresult(nextvar, result, flags) 