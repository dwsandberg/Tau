Module postbind

use seq.findabstractresult

use localmap2

use seq.modExports

use mytype

use seq.mytype

use seq.seq.mytype

use passsymbol

use set.passsymbols

use standard

use symbol

use encoding.symbol

use seq.symbol

use set.symbol

use stack.symbol

use symbol2

use symboldict

use set.symdef

use typedict

function verysimpleinline(sym1:symbol, code:seq.symbol) boolean
if isempty.code ∨ n.code > 10 then
false
else
 let nopara = nopara.sym1
 for isverysimple = n.code ≥ nopara, idx = 1, sym ∈ code
 while isverysimple
 do
  if idx ≤ nopara then
  next(sym = Local.idx, idx + 1)
  else next(
   if isconst.sym then
   true
   else if isBuiltin.sym then
   name.sym ∈ "fld getfld length getseqlength getseqtype"
   else if isInternal.sym then
   name.sym ∉ "idxNB"
   else not.isbr.sym ∧ not.isdefine.sym ∧ not.islocal.sym
   , idx + 1
  ),
 isverysimple ∧ name.sym1 ∉ "decodeword encodeword"

Function postbind(
 exports:seq.word
 , mods:set.passsymbols
 , theprg:set.symdef
 , typedict0:typedict
) midpoint
let discardroots = roots(exports, mods, theprg)
for
 allsyms0 = empty:set.symbol
 , prg1 = empty:set.symdef
 , templates = empty:set.symdef
 , sd ∈ toseq.theprg
do
 if isAbstract.module.sym.sd then
 next(allsyms0, prg1, templates + sd)
 else next(allsyms0 + sym.sd, prg1 + sd, templates)
let allsyms = symboldict.allsyms0
let source = prg1
for
 last = n.encodingdata:symbol
 , result = empty:set.symdef
 , typedict1 = typedict0
 , inline = empty:set.symdef
 , toprocess = encodingdata:symbol
while not.isempty.toprocess
do
 for typedictZ = typedict1, resultZ = result, inlineZ = inline, symz ∈ toprocess
 do
  if isrecordconstant.symz then
   let b = getSymdef(source, symz)
   assert not.isempty.b report "FAIL F"
   for acc = 0, sy ∈ code.1#b do if isrecordconstant.sy then let discard = symbolref.sy, 0 else 0,
   next(typedictZ, resultZ ∪ b, inlineZ)
  else if isspecial.symz ∨ isconst.symz ∨ isBuiltin.symz ∨ isGlobal.symz ∨ inModFor.symz then
  next(typedictZ, resultZ, inlineZ)
  else
   let newdict2 = addtype(typedictZ, resulttype.symz)
   let b = getSymdef(source, symz)
   let sd =
    if not.isempty.b then
    1#b
    else if istype.symz then
    symdef(symz, deepcopybody(resulttype.symz, newdict2), 0)
    else
     let k21 = lookupbysig(allsyms, symz)
     let k2 =
      if n.k21 < 2 then
      k21
      else
       for acc = empty:set.symbol, sy ∈ toseq.k21 do if isunbound.sy then acc else acc + sy,
       if isempty.acc then k21 else acc,
      if isempty.k2 then
      instantiateTemplate(symz, templates)
      else
       assert n.k2 = 1
       report "unbound problem^(symz)
       ^(
        if n.k2 > 1 then
        for txt = "", symt ∈ toseq.k2 do txt + "/br" + library.module.symt + %.symt, txt
        else ""
       )"
       let sym2 = 1#k2
       let b2 = getSymdef(source, sym2),
        if not.isempty.b2 then
         for paras = empty:seq.symbol, i ∈ arithseq(nopara.sym2, 1, 1) do paras + Local.i,
         symdef(sym2, paras + sym2, paragraphno.1#b2)
        else instantiateTemplate(sym2, templates)
   {------------}
   let modpara = para.module.sym.sd
   for
    newdict4 = newdict2
    , cache = empty:set.symdef
    , nextvar = {will be calculated if needed} 0
    , result1 = empty:seq.symbol
    , sym3 ∈ code.sd
   do
    if isrecordconstant.sym3 then
    let discard = symbolref.sym3, next(newdict4, cache, nextvar, result1 + sym3)
    else if isconst.sym3 ∧ not.isFref.sym3 then
    next(newdict4, cache, nextvar, result1 + sym3)
    else if isspecial.sym3 then
     let sym = replaceTsymbol(modpara, sym3)
     let newsym =
      if isloopblock.sym then
       for acc = empty:seq.mytype, p ∈ paratypes.sym do acc + basetype(p, newdict4),
       Loopblock(acc, firstvar.sym, basetype(resulttype.sym, newdict4))
      else if isSequence.sym then
      Sequence(parameter.basetype(resulttype.sym, newdict4), nopara.sym)
      else if isstart.sym then
      Start.basetype(resulttype.sym, newdict4)
      else sym,
     next(newdict4, cache, nextvar, result1 + newsym)
    else
     let sym4 = basesym.sym3
     let sym5 = replaceTsymbol(modpara, sym4)
     let newdict3 = if isSimple.module.sym4 then newdict4 else addtype(newdict4, para.module.sym4),
      if name.sym5 ∈ "pushflds" ∧ isBuiltin.sym5 then
       let typ = para.module.sym5,
       next(
        newdict3
        , cache
        , nextvar
        , if iscore4.typ ∨ isseq.typ ∨ isencoding.typ then
         result1
         else
          let t = flatflds(newdict3, typ),
           if isempty.t ∨ typeT ∈ t then
           result1 + sym5
           else if n.t = 1 then
           result1
           else
            for newresult = result1 >> 1, idx = 0, x ∈ t
            do next(newresult + [1^result1, Lit.idx, Getfld.x], idx + 1),
            newresult
       )
      else
       let result2 = if isFref.sym3 then result1 + PreFref else result1
       let cacheValue = getSymdef(cache, sym4)
       let newValue =
        if not.isempty.cacheValue then
        code.1#cacheValue
        else if isInternal.sym5 then
        let discard = symbolref.sym5, [sym5]
        else if name.sym5 ∈ "idxNB" then
         let orgtype = 1#paratypes.sym5,
          if
           name.symz ∈ "#sequenceIndex"
            ∧ name.module.symz ∈ "seq"
            ∧ abstracttypename.1#paratypes.symz ∈ "pseq"
          then
          {???? why must this case be included?} let discard = symbolref.sym5, [sym5]
          else [symbol(internalmod, "idxNB", orgtype, typeint, basetype(parameter.orgtype, newdict3))]
        else if isBuiltin.sym5 then
        handleBuiltin(sym5, newdict3)
        else
         let xx = getCode(inline, sym5),
         if isempty.xx then let discard = symbolref.sym5, [sym5] else xx << nopara.sym5
       let newValue2 =
        if not.isempty.result2 ∧ 1^result2 = PreFref ∧ n.newValue ≠ 1 then
        {cannot inline Fref} [sym5]
        else newValue,
       next(
        newdict3
        , if isempty.cache then cache + symdef(sym4, newValue, 0) else cache
        , nextvar
        , result2 + newValue2
       ),
   next(
    newdict4
    , symdef4(symz, result1, 0, getOptionsBits.sd) ∪ resultZ
    , if verysimpleinline(symz, result1) ∧ not.isNOINLINE.sd then
     inlineZ + symdef(symz, result1, 0)
     else inlineZ
   )
 let aa = encodingdata:symbol,
 next(n.aa, resultZ, typedictZ, inlineZ, subseq(aa, last + 1, n.aa)),
midpoint5("", result, templates, typedict0, empty:seq.modExports, empty:seq.seq.word)

function %(t:localmap2) seq.word "key: ^(key.t)^(value.t)"

function maxvar(p:symbol, code:seq.symbol) int
for acc = nopara.p, s ∈ code
do
 if isspecial.s then
  if isdefine.s then
  max(acc, value.s)
  else if isloopblock.s then
  max(acc, firstvar.s + nopara.s - 1)
  else acc
 else acc,
acc

function handleBuiltin(sym:symbol, newdict3:typedict) seq.symbol
if name.sym ∈ "finishStart" then
 let geteinfo2Sym = symbol(moduleref."* encodingsupport", "geteinfo2", typeint, typeint, typeptr)
 let updateSym = symbol(moduleref."* encodingsupport", "evectorUpdate", typeptr, typeptr)
 let critial = symbol(internalmod, "critical", [typeint, typeint, typeptr, typeint], typeptr)
 let currentprocess = symbol(internalmod, "currentprocess", typeptr),
 [
  Lit.0
  , currentprocess
  , {paranetprocess} Lit.7
  , Getfld.typeptr
  , PreFref
  , geteinfo2Sym
  , critial
  , updateSym
 ]
else if name.sym ∈ "indirect fromindirect" then
empty:seq.symbol
else if name.sym ∈ "getinstance3" then
 let typ = para.module.sym
 let gl = symbol4(moduleref."internallib $global", 1#"global", typ, empty:seq.mytype, typeptr)
 let mysym = symbol(moduleref."* encodingsupport", "geteinfo", typeptr, seqof.typeword, typeptr)
 let discard = symbolref.mysym,
 [gl, Words.fullprint.typ, mysym]
else if name.sym ∈ "primitiveadd" then
 let T = para.module.sym
 let encodingstatetype = addabstract(typeref."encodingstate encoding *", T)
 let encodingtype = addabstract(typeref."encoding encoding *", T)
 let basetype = basetype(T, newdict3)
 let add2 = symbol(internalmod, {addencoding5} "addencoding5", [typeptr, {typeint} typeptr, typeint], typeint)
 let addefuncx = symbol(moduleref("* encoding", T), "add1encoding", [typeptr, T], encodingtype)
 let discard4 = symbolref.addefuncx
 let discard3 = symbolref.add2
 {if isseq.basetype /or basetype = typeptr then [symbol (internalmod," bitcast", typeptr,
 typeint), PreFref, addefuncx, add2] else assert basetype = typeint report" case not handled"
 [PreFref, addefuncx, add2]}
 [Record.[basetype], PreFref, addefuncx, add2]
else if name.sym ∈ "deepcopy" then
let dc = deepcopySym.para.module.sym let discard2 = symbolref.dc, [dc]
else if name.sym ∈ "bitcast toptr bitcast2" then
 let a = basetype(1#paratypes.sym, newdict3)
 let b = basetype(resulttype.sym, newdict3),
  if (if isseq.a then typeptr else a) = if isseq.b then typeptr else b then
  empty:seq.symbol
  else [symbol(internalmod, "bitcast", a, b)]
else if name.sym ∈ "typestructure" then
 let roottype = para.module.sym
 let tmp =
  for acc = empty:seq.seq.mytype, row ∈ asseqseqmytype.subdict(newdict3, roottype)
  do if 1#row = roottype then [row] + acc else acc + row,
  acc
 {root type is now first row in tmp}
 for acc = empty:seq.symbol, row ∈ tmp
 do
  acc
   + 
   for accrow = empty:seq.symbol, t ∈ row
   do
    let fp = fullprint.t,
     accrow
      + 
      for acctype = empty:seq.symbol, idx = 1, w ∈ fp
      do next(
       acctype
        + if idx < 3 then [Word.w] else [Word.w, Record.[typeword, typeword, typeword]]
       , if idx = 3 then 1 else idx + 1
      ),
      acctype + Sequence(typeword, n.fp / 3),
   accrow + Sequence(seqof.typeptr, n.row),
 acc + Sequence(typeptr, n.tmp)
else [
 if name.sym ∈ "outofbounds" then
 symbol(moduleref."* tausupport", "outofbounds", seqof.typeword)
 else if name.sym ∈ "buildrecord" then
 let t = flatflds(newdict3, para.module.sym), if isempty.t ∨ typeT ∈ t then sym else Record.t
 else if name.sym ∈ "typesize" then
  let typ = para.module.sym,
   if iscore4.typ ∨ isseq.typ then
   Lit.1
   else let t = flatflds(newdict3, typ), if isempty.t ∨ typeT ∈ t then sym else Lit.n.t
 else if name.sym ∈ "packed" then
  let typ = basetype(seqof.para.module.sym, newdict3)
  let tmp = blockitsymbol.typ
  let discard = symbolref.tmp,
  tmp
 else if name.sym ∈ "set set2" then
 setSym.basetype(1^paratypes.sym, newdict3)
 else if name.sym ∈ "fld getfld" then
  let typ = resulttype.sym,
   if iscore4.typ ∨ isseq.typ ∨ isencoding.typ then
   Getfld.typ
   else if isAbstract.typ then
   sym
   else
    let a = flatflds(newdict3, typ)
    assert not.isempty.a report "cannot find type getfld^(typ)",
     if n.a > 1 then
     symbol(internalmod, "GEP", seqof.typeptr, typeint, typeptr)
     else Getfld.1#a
 else if name.sym ∈ "empty" then
 Sequence(basetype(para.module.sym, newdict3), 0)
 else assert name.sym ∈ "createthreadZ" report "post bind error:^(sym)", sym
]

function instantiateTemplate(sym2:symbol, templates:set.symdef) symdef
if isSimple.module.sym2 then
symdef(sym2, empty:seq.symbol, 0)
else
 let gx = findabstract(templates, sym2)
 assert n.gx = 1
 report "Cannot find template for X^(n.gx)^(sym2)
 ^(
  if isempty.gx then
  ""
  else for txt = "", k ∈ gx do txt + "/br" + %.sym.sd.k + %.modpara.k, txt
 )"
 for newcode = empty:seq.symbol, sym4 ∈ code.sd.1#gx
 do newcode + replaceTsymbol(modpara.1#gx, sym4),
 symdef4(sym2, newcode, 0, getOptionsBits.sd.1#gx)

function deepcopybody(type:mytype, typedict:typedict) seq.symbol
if type = typeint ∨ type = typeword ∨ isencoding.type then
[Local.1]
else if isseq.type then
 {base types are int real boolean ptr seq.int seq.real seq.boolean seq.ptr seq.byte seq.
 packed2 seq.packed3 seq.packed4 seq.packed5 seq.packed6}
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
    [Sequence(elementtype, 0)]
     + [Local.theseq, GetSeqLength, Define.totallength]
     + Lit.0
     + Loopblock([theseqtype, typeint], 2, theseqtype)
     + [Local.lastidx, Local.totallength, EqOp, Br2(1, 2), Local.2, Exit]
     + [Local.lastidx, Lit.1, PlusOp, Define.masterindex]
     + [
     Local.theseq
     , Local.masterindex
     , symbol(internalmod, "idxNB", theseqtype, typeint, parameter.theseqtype)
     , Define.theelement
    ]
     + [Local.2, Local.theelement, deepcopySym.parameter.type, cat]
     + [Local.masterindex, continue.2]
     + [EndBlock]
     + blockitsymbol.basetype
else
 let subflds = flatflds(typedict, type),
  if n.subflds = 1 then
   {only one element in record so type is not represent by actual record} [Local.1]
    + deepcopySym.1#subflds
  else
   for fldno = 1, fldkinds = empty:seq.mytype, result = empty:seq.symbol, fldtype ∈ subflds
   do
    let kind = basetype(fldtype, typedict),
    next(
     fldno + 1
     , fldkinds + kind
     , result + [Local.1, Lit(fldno - 1), Getfld.kind, deepcopySym.fldtype]
    ),
   result + [Record.fldkinds]

-------------------------------

type symbolref is toint:int

function symbolref(sym:symbol) symbolref symbolref.addorder.sym

-------------------------------

Function prescan2(s:seq.symdef, typedict:typedict) seq.symdef
{removes name from locals and makes value of local unique.
/br changes length and getseqtype to GetSeqLength and GetSeqType
/br removes next}
for acc = empty:seq.symdef, p ∈ s
do
 for pmap = empty:set.localmap2, parano ∈ arithseq(nopara.sym.p, 1, 1)
 do pmap + localmap2(parano, [Local.parano])
 for
  nextvar = nopara.sym.p + 1
  , map = pmap
  , result = empty:seq.symbol
  , newdict = typedict
  , lastloop = empty:stack.symbol
  , sym ∈ code.p
 do
  if isdefine.sym then
  next(
   nextvar + 1
   , localmap2(value.sym, [Local.nextvar]) ∪ map
   , result + Define.nextvar
   , newdict
   , lastloop
  )
  else if islocal.sym then
  let l = lookup(map, value.sym), next(nextvar, map, result + value.1#l, newdict, lastloop)
  else if isloopblock.sym then
   let offset = nextvar - firstvar.sym
   for newmap = map, v ∈ arithseq(nopara.sym, 1, firstvar.sym)
   do localmap2(v, [Local(v + offset)]) ∪ newmap
   let newsym =
    for acc2 = empty:seq.mytype, para ∈ paratypes.sym do acc2 + basetype(para, newdict),
    Loopblock(acc2, nextvar, basetype(resulttype.sym, newdict)),
   next(
    nextvar + nopara.sym
    , newmap
    , result + newsym
    , add(newdict, typebase.firstvar.sym, [resulttype.sym])
    , push(lastloop, sym)
   )
  else if isExit.sym ∧ name.module.1^result ∈ "$for" ∧ name.1^result ∈ "next" then
   let f = 1^result
   let continueSize = nopara.top.lastloop
   let newresult =
    if continueSize = nopara.f + 1 then
     let l = lookup(map, toint.1#%.parameter.para.module.f + nopara.f + 4),
     result >> 1 + value.1#l
    else result >> 1,
   next(nextvar, map, newresult + continue.continueSize, newdict, lastloop)
  else if sym = EndBlock then
  next(nextvar, map, result + sym, newdict, if isempty.lastloop then lastloop else pop.lastloop)
  else if isstart.sym then
  next(
   nextvar
   , map
   , result + Start.basetype(resulttype.sym, newdict)
   , newdict
   , if isempty.lastloop then lastloop else push(lastloop, top.lastloop)
  )
  else next(
   nextvar
   , map
   , result
    + 
     if not.isBuiltin.sym then
     sym
     else if name.sym ∈ "assert" then
      let typ = basetype(para.module.sym, newdict),
      symbol(internalmod, "assert", seqof.typeword, typeint)
     else if name.sym ∈ "n length" then
     GetSeqLength
     else if name.sym ∈ "getseqtype" then
     GetSeqType
     else if name.sym ∈ "aborted" then
     symbol(internalmod, "processisaborted", typeptr, typeboolean)
     else sym
   , newdict
   , lastloop
  ),
 acc + symdef4(sym.p, result, 0, getOptionsBits.p),
acc

function roots(exports:seq.word, mods:set.passsymbols, prg10:set.symdef) symbolref
for acc = symbolref.outofboundssymbol, f ∈ toseq.mods
do
 if name.module.f ∉ exports then
 acc
 else if isSimple.module.f then
 for acc2 = acc, sym ∈ toseq.exports.f do symbolref.sym, acc2
 else
  for acc2 = empty:seq.symbol, sym ∈ toseq.defines.f do acc2 + getCode(prg10, sym)
  for acc3 = acc, sym2 ∈ toseq.asset.acc2
  do
   if isrecordconstant.sym2 then
   symbolref.sym2
   else if isAbstract.module.sym2 ∨ isconstantorspecial.sym2 ∨ isBuiltin.sym2 ∨ inModFor.sym2 then
   acc3
   else symbolref.sym2,
  acc3,
acc 