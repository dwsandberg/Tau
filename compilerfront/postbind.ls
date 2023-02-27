Module postbind

use seq.commoninfo

use seq.findabstractresult

use localmap2

use mytype

use seq.mytype

use seq.seq.mytype

use passsymbol

use standard

use symbol

use encoding.symbol

use seq.symbol

use set.symbol

use symbol2

use symboldict

use set.symdef

use typedict

function verysimpleinline(sym1:symbol, code:seq.symbol) boolean
if isempty.code ∨ length.code > 10 then
 false
else
 let nopara = nopara.sym1,
 for isverysimple = length.code ≥ nopara, idx = 1, sym ∈ code
 while isverysimple
 do
  if idx ≤ nopara then
   next(sym = Local.idx, idx + 1)
  else
   next(
    if isconst.sym then
     true
    else if isBuiltin.sym then
     name.sym ∈ "fld getfld length getseqlength"
    else if isInternal.sym then
     name.sym ∉ "indexseq45 idxNB"
    else
     not.isbr.sym ∧ not.isdefine.sym ∧ not.islocal.sym
    , idx + 1)
 /do isverysimple ∧ name.sym1 ∉ "decodeword encodeword"

type postbindresult is typedict:typedict, prg:set.symdef, inline:set.symdef

Function postbind(exports:seq.word, mods:set.passsymbols, theprg:set.symdef, typedict1:typedict) midpoint
let discard = roots(exports, mods, theprg),
for allsyms = empty:set.symbol
 , prg1 = empty:set.symdef
 , templates = empty:set.symdef
 , sd ∈ toseq.theprg
do
 if isAbstract.module.sym.sd then
  next(allsyms, prg1, templates + sd)
 else
  next(allsyms + sym.sd, prg1 + sd, templates)
/do
 let r = 
  usedsyms(symboldict(allsyms, empty:seq.commoninfo)
   , prg1
   , 0
   , empty:set.symdef
   , templates
   , typedict1
   , empty:set.symdef)
 ,
 midpoint5("", prg.r, templates, typedict1, empty:seq.modExports, empty:seq.seq.word)

use seq.modExports

function %(t:localmap2) seq.word "key: $(key.t) $(value.t)"

function maxvar(p:symbol, code:seq.symbol) int
for acc = nopara.p, s ∈ code do
 if isspecial.s then
  if isdefine.s then
   max(acc, value.s)
  else if isloopblock.s then max(acc, firstvar.s + nopara.s - 1) else acc
 else
  acc
/do acc

function usedsyms(allsyms:symboldict
 , source:set.symdef
 , last:int
 , result:set.symdef
 , templates:set.symdef
 , typedict1:typedict
 , inline:set.symdef) postbindresult
let aa = encodingdata:symbol,
if length.aa = last then
 postbindresult(typedict1, result, inline)
else
 for accZ = postbindresult(typedict1, result, inline)
  , symz ∈ subseq(aa, last + 1, length.aa)
 do
  if isrecordconstant.symz then
   let b = getSymdef(source, symz)
   assert not.isempty.b report "FAIL F",
   for acc = 0, sy ∈ code.b_1 do
    if isrecordconstant.sy then
     let discard = symbolref.sy,
     0
    else
     0
   /do postbindresult(typedict.accZ, prg.accZ ∪ b, inline.accZ)
  else if isspecial.symz ∨ isconst.symz ∨ isBuiltin.symz ∨ isGlobal.symz ∨ inModFor.symz then
   accZ
  else
   let newdict2 = addtype(typedict.accZ, resulttype.symz)
   let b = getSymdef(source, symz)
   let sd = 
    if not.isempty.b then
     b_1
    else if istype.symz then
     symdef(symz, deepcopybody(resulttype.symz, newdict2), 0)
    else
     let k21 = lookupbysig(allsyms, symz)
     let k2 = 
      if cardinality.k21 < 2 then
       k21
      else
       for acc = empty:set.symbol, sy ∈ toseq.k21 do
        if isunbound.sy then acc else acc + sy
       /do if isempty.acc then k21 else acc
     ,
     if isempty.k2 then
      instantiateTemplate(symz, templates)
     else
      assert cardinality.k2 = 1
      report
       "unbound problem $(symz)
        $(if cardinality.k2 > 1 then
        for txt = "", symt ∈ toseq.k2 do
         txt + "/br" + library.module.symt + %.symt
        /do txt
       else
        ""
       )
        "
      let sym2 = k2_1
      let b2 = getSymdef(source, sym2),
      if not.isempty.b2 then
       for paras = empty:seq.symbol, i ∈ arithseq(nopara.sym2, 1, 1) do
        paras + Local.i
       /do symdef(sym2, paras + sym2, paragraphno.b2_1)
      else
       instantiateTemplate(sym2, templates)
   {------------}
   let modpara = para.module.sym.sd,
   for newdict4 = newdict2
    , cache = empty:set.symdef
    , nextvar = {will be calculated if needed} 0
    , result1 = empty:seq.symbol
    , sym3 ∈ code.sd
   do
    if isrecordconstant.sym3 then
     let discard = symbolref.sym3,
     next(newdict4, cache, nextvar, result1 + sym3)
    else if isconst.sym3 ∧ not.isFref.sym3 then
     next(newdict4, cache, nextvar, result1 + sym3)
    else if isspecial.sym3 then
     let sym = replaceTsymbol(modpara, sym3)
     let newsym = 
      if isloopblock.sym then
       for acc = empty:seq.mytype, p ∈ paratypes.sym do
        acc + basetype(p, newdict4)
       /do Loopblock(acc, firstvar.sym, basetype(resulttype.sym, newdict4))
      else if isSequence.sym then
       Sequence(parameter.basetype(resulttype.sym, newdict4), nopara.sym)
      else if isstart.sym then Start.basetype(resulttype.sym, newdict4) else sym
     ,
     next(newdict4, cache, nextvar, result1 + newsym)
    else
     let sym4 = basesym.sym3
     let sym5 = replaceTsymbol(modpara, sym4)
     let newdict3 = if isSimple.module.sym4 then newdict4 else addtype(newdict4, para.module.sym4),
     if name.sym5 ∈ "pushflds" ∧ isBuiltin.sym5 then
      let typ = para.module.sym5,
      next(newdict3
       , cache
       , nextvar
       , if iscore4.typ ∨ isseq.typ ∨ isencoding.typ then
        result1
       else
        let t = flatflds(newdict3, typ),
        if isempty.t ∨ typeT ∈ t then
         result1 + sym5
        else if length.t = 1 then
         result1
        else
         for newresult = result1 >> 1, idx = 0, x ∈ t do
          next(newresult + [last.result1, Lit.idx, Getfld.x], idx + 1)
         /do newresult
       )
     else
      let result2 = if isFref.sym3 then result1 + PreFref else result1
      let cacheValue = getSymdef(cache, sym4)
      let newValue = 
       if not.isempty.cacheValue then
        code.cacheValue_1
       else if isInternal.sym5 then
        let discard = symbolref.sym5,
        [sym5]
       else if isBuiltin.sym5 then
        handleBuiltin(sym5, newdict3)
       else
        let xx = getCode(inline, sym5),
        if isempty.xx then
         let discard = symbolref.sym5,
         [sym5]
        else
         xx << nopara.sym5
      let newValue2 = 
       if not.isempty.result2 ∧ last.result2 = PreFref ∧ length.newValue ≠ 1 then
        {cannot inline Fref} [sym5]
       else
        newValue
      ,
      next(newdict3
       , if isempty.cache then cache + symdef(sym4, newValue, 0) else cache
       , nextvar
       , result2 + newValue2)
   /do
    postbindresult(newdict4
     , symdef4(symz, result1, 0, getOptionsBits.sd) ∪ prg.accZ
     , if verysimpleinline(symz, result1) ∧ not.isNOINLINE.sd then
      inline.accZ + symdef(symz, result1, 0)
     else
      inline.accZ
     )
 /do usedsyms(allsyms, source, length.aa, prg.accZ, templates, typedict.accZ, inline.accZ)

function handleBuiltin(sym:symbol, newdict3:typedict) seq.symbol
if name.sym ∈ "finishStart" then
 let geteinfo2Sym = symbol(moduleref."* encodingsupport", "geteinfo2", typeint, typeint, typeptr)
 let updateSym = symbol(moduleref."* encodingsupport", "evectorUpdate", typeptr, typeptr)
 let critial = symbol(internalmod, "critical", [typeint, typeint, typeptr, typeint], typeptr)
 let currentprocess = symbol(internalmod, "currentprocess", typeptr),
 [Lit.0
  , currentprocess
  , {paranetprocess} Lit.7
  , Getfld.typeptr
  , PreFref
  , geteinfo2Sym
  , critial
  , updateSym]
else if name.sym ∈ "indirect fromindirect" then
 empty:seq.symbol
else if name.sym ∈ "getinstance3" then
 let typ = para.module.sym
 let gl = symbol4(moduleref."internallib $global", "global"_1, typ, empty:seq.mytype, typeptr)
 let mysym = symbol(moduleref."* encodingsupport", "geteinfo", typeptr, seqof.typeword, typeptr)
 let discard = symbolref.mysym,
 [gl, Words.fullprint.typ, mysym]
else if name.sym ∈ "primitiveadd" then
 let T = para.module.sym
 let encodingstatetype = addabstract(typeref."encodingstate encoding *", T)
 let encodingtype = addabstract(typeref."encoding encoding *", T)
 let basetype = basetype(T, newdict3)
 let add2 = 
  symbol(internalmod
   , {addencoding5} "addencoding5"
   , [typeptr, {typeint} typeptr, typeint]
   , typeint)
 let addefuncx = symbol(moduleref("* encoding", T), "add1encoding", [typeptr, T], encodingtype)
 let discard4 = symbolref.addefuncx
 let discard3 = symbolref.add2,
 {if isseq.basetype /or basetype = typeptr then [symbol (internalmod," bitcast", typeptr, typeint
  ), PreFref, addefuncx, add2] else assert basetype = typeint report" case not handled" [PreFref, addefuncx
  , add2]}
 [Record.[basetype], PreFref, addefuncx, add2]
else if name.sym ∈ "deepcopy" then
 let dc = deepcopySym.para.module.sym
 let discard2 = symbolref.dc,
 [dc]
else if name.sym ∈ "bitcast toptr bitcast2" then
 let a = basetype(first.paratypes.sym, newdict3)
 let b = basetype(resulttype.sym, newdict3),
 if if isseq.a then typeptr else a /if = if isseq.b then typeptr else b then
  empty:seq.symbol
 else
  [symbol(internalmod, "bitcast", a, b)]
else if name.sym ∈ "typestructure" then
 let roottype = para.module.sym
 let tmp = 
  for acc = empty:seq.seq.mytype, row ∈ asseqseqmytype.subdict(newdict3, roottype) do
   if first.row = roottype then [row] + acc else acc + row
  /do acc
 ,
 {root type is now first row in tmp}
 for acc = empty:seq.symbol, row ∈ tmp do
  acc
  + for accrow = empty:seq.symbol, t ∈ row do
   let fp = fullprint.t,
   accrow
   + for acctype = empty:seq.symbol, idx = 1, w ∈ fp do
    next(
     acctype + if idx < 3 then [Word.w] else [Word.w, Record.[typeword, typeword, typeword]]
     , if idx = 3 then 1 else idx + 1)
   /do acctype + Sequence(typeword, length.fp / 3)
  /do accrow + Sequence(seqof.typeptr, length.row)
 /do acc + Sequence(typeptr, length.tmp)
else if name.sym ∈ "_" then
 let seqtype = basetype(first.paratypes.sym, newdict3),
 [symbol(internalmod, "indexseq45", seqtype, typeint, parameter.seqtype)]
else
 [
  if name.sym ∈ "buildrecord" then
   let t = flatflds(newdict3, para.module.sym),
   if isempty.t ∨ typeT ∈ t then sym else Record.t
  else if name.sym ∈ "typesize" then
   let typ = para.module.sym,
   if iscore4.typ ∨ isseq.typ then
    Lit.1
   else
    let t = flatflds(newdict3, typ),
    if isempty.t ∨ typeT ∈ t then sym else Lit.length.t
  else if name.sym ∈ "packed" then
   let typ = basetype(seqof.para.module.sym, newdict3)
   let tmp = blockitsymbol.typ
   let discard = symbolref.tmp,
   tmp
  else if name.sym ∈ "idxNB" then
   let seqtype = basetype(first.paratypes.sym, newdict3),
   symbol(internalmod, "idxNB", seqtype, typeint, parameter.seqtype)
  else if name.sym ∈ "set set2" then
   setSym.basetype(last.paratypes.sym, newdict3)
  else if name.sym ∈ "fld getfld" then
   let typ = resulttype.sym,
   if iscore4.typ ∨ isseq.typ ∨ isencoding.typ then
    Getfld.typ
   else if isAbstract.typ then
    sym
   else
    let a = flatflds(newdict3, typ)
    assert not.isempty.a report "cannot find type getfld $(typ)",
    if length.a > 1 then
     symbol(internalmod, "GEP", seqof.typeptr, typeint, typeptr)
    else
     Getfld.first.a
  else if name.sym ∈ "empty" then
   Sequence(basetype(para.module.sym, newdict3), 0)
  else
   assert name.sym ∈ "createthreadZ" report "post bind error:$(sym)",
   sym
  ]

function instantiateTemplate(sym2:symbol, templates:set.symdef) symdef
if isSimple.module.sym2 then
 symdef(sym2, empty:seq.symbol, 0)
else
 let gx = findabstract(templates, sym2)
 assert length.gx = 1
 report
  "Cannot find template for X $(length.gx) $(sym2)
   $(if isempty.gx then
   ""
  else
   for txt = "", k ∈ gx do txt + "/br" + %.sym.sd.k + %.modpara.k /do txt
  )
   "
 ,
 for newcode = empty:seq.symbol, sym4 ∈ code.sd.gx_1 do
  newcode + replaceTsymbol(modpara.gx_1, sym4)
 /do symdef4(sym2, newcode, 0, getOptionsBits.sd.gx_1)

function deepcopybody(type:mytype, typedict:typedict) seq.symbol
if type = typeint ∨ type = typeword ∨ isencoding.type then
 [Local.1]
else if isseq.type then
 {base types are int real boolean ptr seq.int seq.real seq.boolean seq.ptr seq.byte seq.packed2 seq.packed3
  seq.packed4 seq.packed5 seq.packed6}
 let basetype = basetype(type, typedict)
 let elementtype = parameter.basetype,
 if elementtype = typeboolean then
  [Local.1, blockitsymbol.seqof.typeint]
 else
  let cat = symbol(tomodref.type, "+", [type, parameter.type], type)
  let theseq = 1
  let lastidx = 3
  let theelement = 4
  let totallength = 5
  let masterindex = 6
  let theseqtype = basetype,
  [Sequence(elementtype, 0)] + [Local.theseq, GetSeqLength, Define.totallength] + Lit.0
  + Loopblock([theseqtype, typeint], 2, theseqtype)
  + [Local.lastidx, Local.totallength, EqOp, Br2(1, 2), Local.2, Exit]
  + [Local.lastidx, Lit.1, PlusOp, Define.masterindex]
  + [Local.theseq
   , Local.masterindex
   , symbol(builtinmod.typeint, "idxNB", theseqtype, typeint, parameter.theseqtype)
   , Define.theelement]
  + [Local.2, Local.theelement, deepcopySym.parameter.type, cat]
  + [Local.masterindex, continue.2]
  + [EndBlock, symbol(internalmod, "checkfornoop", basetype, basetype)]
  + blockitsymbol.basetype
else
 let subflds = flatflds(typedict, type),
 if length.subflds = 1 then
  {only one element in record so type is not represent by actual record} [Local.1]
  + deepcopySym.first.subflds
 else
  for fldno = 1
   , fldkinds = empty:seq.mytype
   , result = empty:seq.symbol
   , fldtype ∈ subflds
  do
   let kind = basetype(fldtype, typedict),
   next(fldno + 1
    , fldkinds + kind
    , result + [Local.1, Lit(fldno - 1), Getfld.kind, deepcopySym.fldtype])
  /do result + [Record.fldkinds]

__________________________

type symbolref is toint:int

function symbolref(sym:symbol) symbolref symbolref.addorder.sym

_________________

Function prescan2(s:seq.symdef, typedict:typedict) seq.symdef
{removes name from locals and change length and getseqtype to GetSeqLength and GetSeqType}
for acc = empty:seq.symdef, p ∈ s do
 let pmap = 
  for pmap = empty:set.localmap2, parano ∈ arithseq(nopara.sym.p, 1, 1) do
   pmap + localmap2(parano, [Local.parano])
  /do pmap
 ,
 for nextvar = nopara.sym.p + 1
  , map = pmap
  , result = empty:seq.symbol
  , newdict = typedict
  , sym ∈ code.p
 do
  if isdefine.sym then
   next(nextvar + 1
    , localmap2(value.sym, [Local.nextvar]) ∪ map
    , result + Define.nextvar
    , newdict)
  else if islocal.sym then
   let l = lookup(map, value.sym),
   next(nextvar, map, result + value.l_1, newdict)
  else if isloopblock.sym then
   let offset = nextvar - firstvar.sym
   let newmap = 
    for newmap = map, v ∈ arithseq(nopara.sym, 1, firstvar.sym) do
     localmap2(v, [Local(v + offset)]) ∪ newmap
    /do newmap
   let newsym = 
    for acc2 = empty:seq.mytype, para ∈ paratypes.sym do
     acc2 + basetype(para, newdict)
    /do Loopblock(acc2, nextvar, basetype(resulttype.sym, newdict))
   ,
   next(nextvar + nopara.sym
    , newmap
    , result + newsym
    , add(newdict, typebase.firstvar.sym, [resulttype.sym]))
  else if isExit.sym ∧ name.module.last.result ∈ "$for" ∧ name.last.result ∈ "next" then
   let f = last.result
   let l = lookup(map, toint.first.%.parameter.para.module.f + nopara.f + 4)
   let newresult = value.l_1,
   next(nextvar, map, result >> 1 + newresult + continue(nopara.f + 1), newdict)
  else
   next(nextvar
    , map
    , result
    + if isstart.sym then
     Start.basetype(resulttype.sym, newdict)
    else if not.isBuiltin.sym then
     sym
    else if name.sym ∈ "assert" then
     let typ = basetype(para.module.sym, newdict),
     symbol(internalmod, "assert", seqof.typeword, typeint)
    else if name.sym ∈ "length" then
     GetSeqLength
    else if name.sym ∈ "getseqtype" then
     GetSeqType
    else if name.sym ∈ "aborted" then
     symbol(internalmod, "processisaborted", typeptr, typeboolean)
    else
     sym
    , newdict)
 /do acc + symdef4(sym.p, result, 0, getOptionsBits.p)
/do acc

use set.passsymbols

function roots(exports:seq.word, mods:set.passsymbols, prg10:set.symdef) symbolref
for acc = symbolref.outofboundssymbol, f ∈ toseq.mods do
 if name.module.f ∉ exports then
  acc
 else if isSimple.module.f then
  for acc2 = acc, sym ∈ toseq.exports.f do symbolref.sym /do acc2
 else
  for acc2 = empty:seq.symbol, sym ∈ toseq.defines.f do
   acc2 + getCode(prg10, sym)
  /do
   for acc3 = acc, sym2 ∈ toseq.asset.acc2 do
    if isrecordconstant.sym2 then
     symbolref.sym2
    else if isAbstract.module.sym2 ∨ isconstantorspecial.sym2 ∨ isBuiltin.sym2 ∨ inModFor.sym2 then
     acc3
    else
     symbolref.sym2
   /do acc3
/do acc 