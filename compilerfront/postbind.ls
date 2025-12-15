Module postbind

use seq.findabstractresult

use localmap2

use seq.modExports

use mytype

use seq1.mytype

use seq.mytype

use seq.seq.mytype

use passsymbol

use set.passsymbols

use standard

use encoding.symbol

use seq.symbol

use set.symbol

use stack.symbol

use symbol1

use symboldict

use set.symdef

use typedict

function verysimpleinline(sym1:symbol, code:seq.symbol) boolean
if isempty.code ∨ n.code > 10 then false
else
 let nopara = nopara.sym1
 for isverysimple = n.code ≥ nopara, idx = 1, sym ∈ code
 while isverysimple
 do
  let kind = kind.sym,
  next(
   if isconst.kind ∨ kind = kfld then true
   else if kind = klocal then idx ≤ nopara ∧ value.sym = idx
   else
    kind
    ∉ [
     kstart
     , kloop
     , kidxNB
     , kother
     , kcompoundname
     , kcat
     , kidx
     , kmakereal
     , kmember
     , kdefine
     , kglobal
    ]
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
 if isAbstract.module.sym.sd then next(allsyms0, prg1, templates + sd)
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
  if kind.symz = kconstantrecord then
   let b = getSymdef(source, symz)
   assert not.isempty.b report "FAIL F",
   for acc = 0, sy ∈ code.b sub 1
   do
    if kind.sy = kconstantrecord then
     let discard = symbolref.sy,
     0
    else 0,
   next(typedictZ, resultZ ∪ b, inlineZ)
  else if isconstantorspecial.symz ∨ isBuiltin.symz ∨ kind.symz = kglobal then next(typedictZ, resultZ, inlineZ)
  else
   let newdict2 = addtype(typedictZ, resulttype.symz)
   let b = getSymdef(source, symz)
   let sd =
    if not.isempty.b then b sub 1
    else if istype.symz then symdef(symz, deepcopybody(resulttype.symz, newdict2), 0)
    else
     let k21 = lookupbysig(allsyms, symz)
     let k2 =
      if n.k21 < 2 then k21
      else
       for acc = empty:set.symbol, sy ∈ toseq.k21 do if isunbound.sy then acc else acc + sy,
       if isempty.acc then k21 else acc,
     if isempty.k2 then instantiateTemplate(symz, templates)
     else
      assert n.k2 = 1 report
       "unbound problem:(symz):(if n.k2 > 1 then
        for txt = "", symt ∈ toseq.k2 do txt + "/br" + library.module.symt + %.symt,
        txt
       else "")"
      let sym2 = k2 sub 1,
      let b2 = getSymdef(source, sym2),
      if not.isempty.b2 then
       for paras = empty:seq.symbol, i ∈ arithseq(nopara.sym2, 1, 1) do paras + Local.i,
       symdef(sym2, paras + sym2, paragraphno.b2 sub 1)
      else instantiateTemplate(sym2, templates)
   {------------}
   let modpara = para.module.sym.sd,
   for
    newdict4 = newdict2
    , cache = empty:set.symdef
    , nextvar = {will be calculated if needed}0
    , result1 = empty:seq.symbol
    , sym3 ∈ code.sd
   do
    let kind = kind.sym3
    let sym4 = basesym.sym3,
    let sym5 = replaceTsymbol(modpara, sym4),
    if between(kind, kwords, kendblock) then
     let newsym =
      if kind = kconstantrecord then
       let discard = symbolref.sym5,
       sym5
      else if kind = kloop then Loopblock(basetype(paratypes.sym5, newdict4), firstvar.sym5, basetype(resulttype.sym5, newdict4))
      else if kind = ksequence then Sequence(parameter.basetype(resulttype.sym5, newdict4), nopara.sym5)
      else if kind = kstart then Start.basetype(resulttype.sym5, newdict4)
      else sym5,
     next(newdict4, cache, nextvar, result1 + newsym)
    else
     let newdict3 =
      if isSimple.module.sym4 then newdict4 else addtype(newdict4, para.module.sym4),
     if name.sym5 ∈ "pushflds" ∧ isBuiltin.sym5 then
      let typ = para.module.sym5,
      next(
       newdict3
       , cache
       , nextvar
       , if iscore4.typ ∨ isseq.typ ∨ isencoding.typ then result1
       else
        let t = flatflds(newdict3, typ),
        if isempty.t ∨ typeT ∈ t then result1 + sym5
        else if n.t = 1 then result1
        else
         for newresult = result1 >> 1, idx = 0, x ∈ t
         do next(newresult + [result1 sub n.result1, Lit.idx, Getfld.x], idx + 1),
         newresult
      )
     else
      let cacheValue = getSymdef(cache, sym4)
      let newValue =
       if not.isempty.cacheValue then code.cacheValue sub 1
       else if name.sym5 ∈ "idxNB" then [symIdxNB.parameter.basetype((paratypes.sym5) sub 1, newdict3)]
       else if isBuiltin.sym5 then handleBuiltin(sym5, newdict3)
       else if kind.sym5 ∉ isOrdinary then
        let discard = symbolref.sym5,
        [sym5]
       else
        let xx = getCode(inline, sym5),
        if isempty.xx then
         let discard = symbolref.sym5,
         [sym5]
        else xx << nopara.sym5
      let result2 = if kind.sym3 = kfref then result1 + PreFref else result1,
      let newValue2 =
       if not.isempty.result2 ∧ kind.result2 sub n.result2 = kprefref ∧ n.newValue ≠ 1 then{cannot inline Fref}[sym5]
       else newValue,
      next(
       newdict3
       , if isempty.cache then cache + symdef(sym4, newValue, 0) else cache
       , nextvar
       , result2 + newValue2
      ),
   next(
    newdict4
    , symdef4(symz, result1, 0, options.sd) ∪ resultZ
    , if verysimpleinline(symz, result1) ∧ NOINLINE ∉ options.sd then inlineZ + symdef(symz, result1, 0)
    else inlineZ
   )
 let aa = encodingdata:symbol,
 next(n.aa, resultZ, typedictZ, inlineZ, subseq(aa, last + 1, n.aa)),
midpoint5("", result, templates, typedict0, empty:seq.modExports, empty:seq.seq.word)

function %(t:localmap2) seq.word "key: :(key.t):(value.t)"

function maxvar(p:symbol, code:seq.symbol) int
for acc = nopara.p, s ∈ code
do
 let kind = kind.s,
 if kind = kdefine then max(acc, value.s)
 else if kind = kloop then max(acc, firstvar.s + nopara.s - 1)
 else acc,
acc

function blockitsymbol(T:mytype) seq.symbol
let para = parameter.T,
if para ∈ [typeint, typeptr, typereal] then[symbol(moduleref("* taublockseq", para), "blockit3", [T], T)]
else
 let i =
  findindex([typepacked2, typepacked3, typepacked4, typepacked5, typepacked6], para),
 if i < 6 then[Lit(i + 1), symbol(moduleref("* taublockseq", para), "blockit2", [T, typeint], T)]
 else
  assert para = typebyte report "????:(T)",
  [symbol(moduleref."* tausupport", "blockIt", [T], T)]

function handleBuiltin(sym:symbol, newdict3:typedict) seq.symbol
if name.sym ∈ "finishStart" then
 let geteinfo2Sym =
  symbol(moduleref."* encodingsupport", "geteinfo2", [typeint, typeint], typeptr)
 let updateSym = symbol(moduleref."* encodingsupport", "evectorUpdate", [typeptr], typeptr)
 let critial =
  symbol(internalmod, "critical", [typeint, typeint, typeptr, typeint], typeptr),
 let currentprocess = symbol(internalmod, "currentprocess", typeptr),
 [
  Lit.0
  , currentprocess
  , {paranetprocess}Lit.7
  , Getfld.typeptr
  , PreFref
  , geteinfo2Sym
  , critial
  , updateSym
 ]
else if name.sym ∈ "indirect fromindirect" then empty:seq.symbol
else if name.sym ∈ "getinstance3" then
 let typ = para.module.sym
 let gl =
  symbol4(moduleref."internallib $global", "global" sub 1, typ, empty:seq.mytype, typeptr)
 let mysym =
  symbol(moduleref."* encodingsupport", "geteinfo", [typeptr, seqof.typeword], typeptr),
 let discard = symbolref.mysym,
 [gl, Words.fullprint.typ, mysym]
else if name.sym ∈ "primitiveadd" then
 let T = para.module.sym
 let encodingstatetype = addabstract(typeref."encodingstate encoding *", T)
 let encodingtype = addabstract(typeref."encoding encoding *", T)
 let basetype = basetype(T, newdict3)
 let add2 =
  symbol(
   internalmod
   , {addencoding5} "addencoding5"
   , [typeptr, {typeint}typeptr, typeint]
   , typeint
  )
 let addefuncx =
  symbol(moduleref("* encoding", T), "add1encoding", [typeptr, T], encodingtype)
 let discard4 = symbolref.addefuncx,
 let discard3 = symbolref.add2,
 [Record.[basetype], PreFref, addefuncx, add2]
else if name.sym ∈ "deepcopy" then
 let dc = deepcopySym.para.module.sym
 let discard2 = symbolref.dc,
 [dc]
else if name.sym ∈ "bitcast toptr bitcast2" then
 let a = basetype((paratypes.sym) sub 1, newdict3)
 let b = basetype(resulttype.sym, newdict3),
 if (if isseq.a then typeptr else a) = (if isseq.b then typeptr else b) then empty:seq.symbol
 else [symbol(internalmod, "bitcast", [a], b)]
else if name.sym ∈ "typestructure" then
 let roottype = para.module.sym
 let tmp =
  for acc = empty:seq.seq.mytype, row ∈ asseqseqmytype.subdict(newdict3, roottype)
  do if row sub 1 = roottype then [row] + acc else acc + row,
  acc
 {root type is now first row in tmp}
 for acc = empty:seq.symbol, row ∈ tmp
 do
  acc
  + for accrow = empty:seq.symbol, t ∈ row
  do
   let fp = fullprint.t,
   accrow
   + for acctype = empty:seq.symbol, idx = 1, w ∈ fp
   do
    next(
     acctype
     + (if idx < 3 then [Word.w] else [Word.w, Record.[typeword, typeword, typeword]])
     , if idx = 3 then 1 else idx + 1
    ),
   acctype + Sequence(typeword, n.fp / 3),
  accrow + Sequence(seqof.typeptr, n.row),
 acc + Sequence(typeptr, n.tmp)
else if name.sym ∈ "packed" then
 let typ = basetype(seqof.para.module.sym, newdict3),
 blockitsymbol.typ
else
 [
  if name.sym ∈ "outofbounds" then symbol(moduleref."* tausupport", "outofbounds", seqof.typeword)
  else if name.sym ∈ "buildrecord" then
   let t = flatflds(newdict3, para.module.sym),
   if isempty.t ∨ typeT ∈ t then sym else Record.t
  else if name.sym ∈ "typesize" then
   let typ = para.module.sym,
   if iscore4.typ ∨ isseq.typ then Lit.1
   else
    let t = flatflds(newdict3, typ),
    if isempty.t ∨ typeT ∈ t then sym else Lit.n.t
  else if name.sym ∈ "set" then
   let ptypes = paratypes.sym,
   setSym.basetype(ptypes sub n.ptypes, newdict3)
  else if name.sym ∈ "fld getfld" then
   let typ = resulttype.sym,
   if iscore4.typ ∨ isseq.typ ∨ isencoding.typ then Getfld.typ
   else if isAbstract.typ then sym
   else
    let a = flatflds(newdict3, typ)
    assert not.isempty.a report "cannot find type getfld:(typ)",
    if n.a > 1 then symbol(internalmod, "GEP", [seqof.typeptr, typeint], typeptr)
    else Getfld.a sub 1
  else if name.sym ∈ "empty" then Sequence(basetype(para.module.sym, newdict3), 0)
  else
   assert kind.sym = kcreatethreadZ report "post bind error::(sym)",
   sym
 ]

function instantiateTemplate(sym2:symbol, templates:set.symdef) symdef
if isSimple.module.sym2 then symdef(sym2, empty:seq.symbol, 0)
else
 let gx = findabstract(templates, sym2)
 let tmp =
  if n.gx = 2
  ∧ not.isSimple.modpara.gx sub 1
  ∧ parameter.modpara.gx sub 1 = modpara.gx sub 2 then{???? generalize?}gx sub 2
  else
   assert n.gx = 1 report
    "Cannot find template for X:(n.gx):(sym2):(if isempty.gx then
     {for txt ="", e ∈toseq.templates do if name.sym.e = name.sym2 then txt+"/br
     :(sym.e)"else txt}
     ""
    else
     for txt = "", k ∈ gx do txt + "/br" + %.sym.sd.k + %.modpara.k,
     txt
    )",
   gx sub 1,
 for newcode = empty:seq.symbol, sym4 ∈ code.sd.tmp
 do
  newcode
  + if kind.sym4 = krecord then
   for newtypes = empty:seq.mytype, e ∈ paratypes.sym4 do newtypes + replaceT(modpara.tmp, e),
   if newtypes = paratypes.sym4 then sym4 else Record.newtypes
  else replaceTsymbol(modpara.tmp, sym4),
 symdef4(sym2, newcode, 0, options.sd.tmp)

function deepcopybody(type:mytype, typedict:typedict) seq.symbol
if type = typeint ∨ type = typeword ∨ isencoding.type then [Local.1]
else if isseq.type then
 {base types are int real boolean ptr seq.int seq.real seq.boolean seq.ptr seq.byte seq.packed2 seq.packed3 seq.packed4 seq.packed5 seq.packed6}
 let basetype = basetype(type, typedict)
 let elementtype = parameter.basetype
 let cat = symbol(tomodref.type, "+", [type, parameter.type], type)
 let theseq = 1
 let lastidx = 3
 let theelement = 4
 let totallength = 5
 let masterindex = 6,
 let theseqtype = basetype,
 [Sequence(elementtype, 0)]
 + [Local.theseq, GetSeqLength, Define.totallength]
 + Lit.0
 + Loopblock([theseqtype, typeint], 2, theseqtype)
 + [Local.lastidx, Local.totallength, EqOp, Br2(1, 2), Local.2, Exit]
 + [Local.lastidx, Lit.1, PlusOp, Define.masterindex]
 + [Local.theseq, Local.masterindex, symIdxNB.parameter.theseqtype, Define.theelement]
 + [Local.2, Local.theelement, deepcopySym.parameter.type, cat]
 + [Local.masterindex, continue.2]
 + [EndBlock]
 + blockitsymbol.basetype
else
 let subflds = flatflds(typedict, type),
 if n.subflds = 1 then
  {only one element in record so type is not represent by actual record}[Local.1]
  + deepcopySym.subflds sub 1
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
{removes name from locals and makes value of local unique./br
changes length and getseqtype to GetSeqLength and GetSeqType /br
removes next in for loops}
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
  let kind = kind.sym,
  if kind = kdefine then
   next(
    nextvar + 1
    , localmap2(value.sym, [Local.nextvar]) ∪ map
    , result + Define.nextvar
    , newdict
    , lastloop
   )
  else if kind = klocal then
   let l = lookup(map, value.sym),
   next(nextvar, map, result + value.l sub 1, newdict, lastloop)
  else if kind = kloop then
   let offset = nextvar - firstvar.sym
   for newmap = map, v ∈ arithseq(nopara.sym, 1, firstvar.sym)
   do localmap2(v, [Local(v + offset)]) ∪ newmap,
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
  else if kind = kexit
  ∧ name.module.result sub n.result ∈ "$for"
  ∧ name.result sub n.result ∈ "next" then
   let f = result sub n.result
   let continueSize = nopara.top.lastloop,
   let newresult =
    if continueSize = nopara.f + 1 then
     let l = lookup(map, toint.(%.parameter.para.module.f) sub 1 + nopara.f + 4),
     result >> 1 + value.l sub 1
    else result >> 1,
   next(nextvar, map, newresult + continue.continueSize, newdict, lastloop)
  else if kind = kendblock then
   next(
    nextvar
    , map
    , result + sym
    , newdict
    , if isempty.lastloop then lastloop else pop.lastloop
   )
  else if kind = kstart then
   next(
    nextvar
    , map
    , result + Start.basetype(resulttype.sym, newdict)
    , newdict
    , if isempty.lastloop then lastloop else push(lastloop, top.lastloop)
   )
  else
   next(
    nextvar
    , map
    , result
    + (if not.isBuiltin.sym then sym
    else if name.sym ∈ "assert" then
     let typ = basetype(para.module.sym, newdict),
     symbol(internalmod, "assert", [seqof.typeword], typeint)
    else if name.sym ∈ "n" then GetSeqLength
    else if name.sym ∈ "getseqtype" then GetSeqType
    else if name.sym ∈ "aborted" then symbol(internalmod, "processisaborted", [typeptr], typeboolean)
    else sym)
    , newdict
    , lastloop
   ),
 acc + symdef4(sym.p, result, 0, options.p),
acc

function roots(exports:seq.word, mods:set.passsymbols, prg10:set.symdef) symbolref
let all = "*" sub 1 ∈ exports
for acc = symbolref.outofboundssymbol, f ∈ toseq.mods
do
 if not.all ∧ name.module.f ∉ exports then acc
 else if isSimple.module.f then
  for acc2 = acc, sym ∈ toseq.exports.f do symbolref.sym,
  acc2
 else
  for acc2 = empty:seq.symbol, sym ∈ toseq.defines.f do acc2 + getCode(prg10, sym)
  for acc3 = acc, sym2 ∈ toseq.asset.acc2
  do
   if isAbstract.module.sym2 then acc3
   else if kind.sym2 = kconstantrecord then symbolref.sym2
   else if false then if kind.sym2 ∈ isOrdinary then symbolref.sym2 else acc3
   else if isconstantorspecial.sym2 ∨ isBuiltin.sym2 then acc3
   else
    {assert kind.sym2 ∈(isOrdinary+[knot, kinternalmod])report"GG5:(kind.sym2)"}
    symbolref.sym2,
  acc3,
acc

function isBuiltin(sym:symbol) boolean name.module.sym = "builtin" sub 1 