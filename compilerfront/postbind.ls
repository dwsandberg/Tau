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

Export prg(postbindresult) set.symdef

Export typedict(postbindresult) typedict

function verysimpleinline(sym1:symbol, code:seq.symbol) boolean
if isempty.code ∨ length.code > 10 then
 false
else
 let nopara = nopara.sym1
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
 /for (isverysimple ∧ name.sym1 ∉ "decodeword encodeword")

type postbindresult is typedict:typedict, prg:set.symdef, inline:set.symdef

Function postbind(roots:seq.symbol, theprg:set.symdef, templates:set.symdef, typedict1:typedict) postbindresult
let discard = for acc = symbolref.Lit.0, r ∈ roots do symbolref.r /for (0)
for allsyms = empty:set.symbol, sd ∈ toseq.theprg do
 allsyms + sym.sd
/for (
 usedsyms(symboldict(allsyms, empty:seq.commoninfo)
  , theprg
  , 0
  , empty:set.symdef
  , templates
  , typedict1
  , empty:set.symdef)
)

function %(t:localmap2) seq.word "key: $(key.t) $(value.t)"

function usedsyms(allsyms:symboldict
 , source:set.symdef
 , last:int
 , result:set.symdef
 , templates:set.symdef
 , typedict1:typedict
 , inline:set.symdef) postbindresult
let aa = encodingdata:symbol
if length.aa = last then
 postbindresult(typedict1, result, inline)
else
 for accZ = postbindresult(typedict1, result, inline)
  , symz ∈ subseq(aa, last + 1, length.aa)
 do
  if isspecial.symz ∨ isconst.symz ∨ isBuiltin.symz ∨ isGlobal.symz ∨ inModFor.symz then
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
       /for (if isempty.acc then k21 else acc)
     if isempty.k2 then
      instantiateTemplate(symz, templates)
     else
      assert cardinality.k2 = 1
      report
       "unbound problem $(symz) $(if cardinality.k2 > 1 then
        for txt = "
         ", symt ∈ toseq.k2 do
         txt + "
          /br" + library.module.symt + %.symt
        /for (txt)
       else
        ""
       )"
      let sym2 = k2_1
      let b2 = getSymdef(source, sym2)
      if not.isempty.b2 then
       for paras = empty:seq.symbol, i ∈ arithseq(nopara.sym2, 1, 1) do
        paras + Local.i
       /for (symdef(sym2, paras + sym2, paragraphno.b2_1))
      else
       instantiateTemplate(sym2, templates)
   {------------}
   let modpara = para.module.sym.sd
   let pdict = 
    for pmap = empty:set.localmap2, parano ∈ arithseq(nopara.sym.sd, 1, 1) do
     pmap + localmap2(parano, [Local.parano])
    /for (pmap)
   for newdict4 = newdict2
    , cache = empty:set.symdef
    , nextvar = nopara.sym.sd + 1
    , map = pdict
    , result2 = empty:seq.symbol
    , symx ∈ code.sd
   do
    let sym = replaceTsymbol(modpara, symx)
    if isconst.sym then
     next(newdict4, cache, nextvar, map, result2 + sym)
    else if isspecial.sym then
     if name.module.sym ∈ "$define" then
      next(newdict4
       , cache
       , nextvar + 1
       , localmap2(value.sym, [Local.nextvar]) ∪ map
       , result2 + Define.nextvar)
     else if name.module.sym ∈ "$local" then
      let l = lookup(map, value.sym)
      let t = value.l_1
      next(newdict4, cache, nextvar, map, result2 + t)
     else if isloopblock.sym then
      let offset = nextvar - firstvar.sym
      let newmap = 
       for newmap = map, v ∈ arithseq(nopara.sym, 1, firstvar.sym) do
        localmap2(v, [Local(v + offset)]) ∪ newmap
       /for (newmap)
      let newsym = 
       for acc = empty:seq.mytype, p ∈ paratypes.sym do
        acc + basetype(p, newdict4)
       /for (Loopblock(acc, nextvar, basetype(resulttype.sym, newdict4)))
      next(newdict4, cache, nextvar + nopara.sym, newmap, result2 + newsym)
     else if isSequence.sym then
      let newsym = Sequence(parameter.basetype(resulttype.sym, newdict4), nopara.sym)
      next(newdict4, cache, nextvar, map, result2 + newsym)
     else if isstart.sym then
      let newsym = Start.basetype(resulttype.sym, newdict4)
      next(newdict4, cache, nextvar, map, result2 + newsym)
     else
      next(newdict4, cache, nextvar, map, result2 + sym)
    else
     let newdict3 = if issimple.module.symx then newdict4 else addtype(newdict4, para.module.symx)
     if name.sym ∈ "primitiveadd primitive2add" ∧ isBuiltin.sym then
      let T = para.module.sym
      let encodingstatetype = addabstract(typeref."encodingstate encoding *", T)
      let encodingpairtype = addabstract(typeref."encodingpair encoding *", T)
      let addefunc = 
       symbol(moduleref("* encoding", T)
        , "add"
        , [encodingstatetype, encodingpairtype]
        , encodingstatetype)
      let add2 = symbol(internalmod, "addencoding", [typeint, typeptr, typeint, typeint], typeint)
      let dc = deepcopySym.encodingpairtype
      let discard = symbolref.addefunc
      let discard2 = symbolref.dc
      let discard3 = symbolref.add2
      let addefuncx = 
       symbol(moduleref("* encoding", T)
        , "addencoding"
        , [encodingstatetype, T]
        , encodingstatetype)
      let dcx = deepcopySym.T
      let discard4 = symbolref.addefuncx
      let discard5 = symbolref.dcx
      if name.sym ∈ "primitive2add" then
       next(newdict3
        , cache
        , nextvar + 1
        , map
        , result2 + [PreFref, addefuncx, PreFref, dcx, add2])
      else
       next(newdict3
        , cache
        , nextvar + 1
        , map
        , result2 + [PreFref, addefunc, PreFref, dc, add2])
     else if name.sym ∈ "getinstance" ∧ isBuiltin.sym then
      let get = symbol(internalmod, "getinstance", typeint, typeptr)
      let typ = para.module.sym
      let gl = 
       symbol4(moduleref."internallib $global"
        , "global"_1
        , typ
        , empty:seq.mytype
        , seqof.typeint)
      let encodenocode = 
       if typ = typeref."typename tausupport *" then
        [Lit.2]
       else if typ = seqof.typechar then
        [Lit.1]
       else
        let discard = symbolref.encodenosym
        ifthenelse([gl, Lit.0, Getfld.typeint, Define.nextvar, Local.nextvar, Lit.0, EqOp]
         , [gl
          , Words.fullprint.typ
          , encodenosym
          , setSym.typeint
          , Define(nextvar + 1)
          , gl
          , Lit.0
          , Getfld.typeint]
         , [Local.nextvar]
         , typeint)
      next(newdict3, cache, nextvar + 2, map, result2 + encodenocode + get)
     else if name.sym ∈ "pushflds" ∧ isBuiltin.sym then
      let typ = para.module.sym
      next(newdict3
       , cache
       , nextvar
       , map
       , if iscore4.typ ∨ isseq.typ ∨ isencoding.typ then
        result2
       else
        let t = flatflds(newdict3, typ)
        if isempty.t ∨ typeT ∈ t then
         result2 + sym
        else if length.t = 1 then
         result2
        else
         for newresult = result2 >> 1, idx = 0, x ∈ t do
          next(newresult + [last.result2, Lit.idx, Getfld.x], idx + 1)
         /for (newresult)
       )
     else if not.isempty.result2 ∧ last.result2 = PreFref then
      next(newdict3
       , cache
       , nextvar
       , map
       , result2 + test3(replaceTsymbol(modpara, symx), newdict3, empty:set.symdef))
     else
      let cacheValue = getSymdef(cache, symx)
      if not.isempty.cacheValue then
       next(newdict3, cache, nextvar, map, result2 + code.cacheValue_1)
      else
       let newValue = test3(replaceTsymbol(modpara, symx), newdict3, inline.accZ)
       next(newdict3, cache + symdef(symx, newValue, 0), nextvar, map, result2 + newValue)
   /for (
    postbindresult(newdict4
     , symdef4(symz, result2, 0, getOptionsBits.sd) ∪ prg.accZ
     , if verysimpleinline(symz, result2) then
      inline.accZ + symdef(symz, result2, 0)
     else
      inline.accZ
     )
   )
 /for (usedsyms(allsyms, source, length.aa, prg.accZ, templates, typedict.accZ, inline.accZ))

function test3(sym:symbol, newdict3:typedict, inline:set.symdef) seq.symbol
{isspecail.sym will be false}
if isInternal.sym then
 let discard = symbolref.sym
 [sym]
else if not.isBuiltin.sym then
 let xx = getCode(inline, sym)
 if isempty.xx then
  let discard = symbolref.sym
  [sym]
 else
  xx << nopara.sym
else if name.sym ∈ "bitcast toptr" then
 let a = basetype(first.paratypes.sym, newdict3)
 let b = basetype(resulttype.sym, newdict3)
 if if isseq.a then typeptr else a /if = if isseq.b then typeptr else b then
  empty:seq.symbol
 else
  [symbol(internalmod, "bitcast", a, b)]
else if name.sym ∈ "processresult" then
 [Lit.2, Getfld.basetype(para.module.sym, newdict3)]
else if name.sym ∈ "typestructure" then
 let roottype = para.module.sym
 let tmp = 
  for acc = empty:seq.seq.mytype, row ∈ asseqseqmytype.subdict(newdict3, roottype) do
   if first.row = roottype then [row] + acc else acc + row
  /for (acc)
 {root type is now first row in tmp}
 for acc = empty:seq.symbol, row ∈ tmp do
  acc
  + for accrow = empty:seq.symbol, t ∈ row do
   let fp = fullprint.t
   accrow
   + for acctype = empty:seq.symbol, idx = 1, w ∈ fp do
    next(acctype + if idx < 3 then [Word.w] else [Word.w, Record.[typeword, typeword, typeword]]
     , if idx = 3 then 1 else idx + 1)
   /for (acctype + Sequence(typeword, length.fp / 3))
  /for (accrow + Sequence(seqof.typeptr, length.row))
 /for (acc + Sequence(typeptr, length.tmp))
else if name.sym ∈ "_" then
 let seqtype = basetype(first.paratypes.sym, newdict3)
 [symbol(internalmod, "indexseq45", seqtype, typeint, parameter.seqtype)]
else
 [
  if name.sym ∈ "buildrecord" then
   let t = flatflds(newdict3, para.module.sym)
   if isempty.t ∨ typeT ∈ t then sym else Record.t
  else if name.sym ∈ "typesize" then
   let typ = para.module.sym
   if iscore4.typ ∨ isseq.typ then
    Lit.1
   else
    let t = flatflds(newdict3, typ)
    if isempty.t ∨ typeT ∈ t then sym else Lit.length.t
  else if name.sym ∈ "packed" then
   let typ = basetype(seqof.para.module.sym, newdict3)
   let tmp = blockitsymbol.typ
   let discard = symbolref.tmp
   tmp
  else if name.sym ∈ "assert" then
   abortsymbol.basetype(para.module.sym, newdict3)
  else if name.sym ∈ "idxNB" then
   let seqtype = basetype(first.paratypes.sym, newdict3)
   symbol(internalmod, "idxNB", seqtype, typeint, parameter.seqtype)
  else if name.sym ∈ "set" then
   setSym.basetype(para.module.sym, newdict3)
  else if name.sym = "createthreadY"_1 then
   let paras = 
    for paras = empty:seq.mytype, p ∈ paratypes.sym do
     let tmp = basetype(p, newdict3)
     paras + if isseq.tmp then typeptr else tmp
    /for (paras)
   let rt = basetype(parameter.resulttype.sym, newdict3)
   symbol(builtinmod.processof.if isseq.rt then typeptr else rt
    , "createthreadY"
    , paras
    , typeptr)
  else if name.sym ∈ "fld getfld" then
   let typ = resulttype.sym
   if iscore4.typ ∨ isseq.typ ∨ isencoding.typ then
    Getfld.typ
   else if isabstract.typ then
    sym
   else
    let a = flatflds(newdict3, typ)
    assert not.isempty.a report "cannot find type getfld $(typ)"
    if length.a > 1 then
     symbol(internalmod, "GEP", seqof.typeptr, typeint, typeptr)
    else
     Getfld.first.a
  else if name.sym ∈ "empty" then
   Sequence(basetype(para.module.sym, newdict3), 0)
  else
   assert name.sym ∈ "xoffsets xbuild" report "post bind error:$(sym)"
   sym
  ]

function instantiateTemplate(sym2:symbol, templates:set.symdef) symdef
if issimple.module.sym2 then
 symdef(sym2, empty:seq.symbol, 0)
else
 let gx = findabstract(templates, sym2)
 assert length.gx = 1
 report
  "Cannot find template for X $(length.gx) $(sym2) $(if isempty.gx then
   ""
  else
   for txt = "
    ", k ∈ gx do txt + "
    /br" + %.sym.sd.k + %.modpara.k /for (txt)
  )"
 for newcode = empty:seq.symbol, sym4 ∈ code.sd.gx_1 do
  newcode + replaceTsymbol(modpara.gx_1, sym4)
 /for (symdef4(sym2, newcode, 0, getOptionsBits.sd.gx_1))

function deepcopybody(type:mytype, typedict:typedict) seq.symbol
if type = typeint ∨ type = typeword ∨ isencoding.type then
 [Local.1]
else if isseq.type then
 {base types are int real boolean ptr seq.int seq.real seq.boolean seq.ptr seq.byte seq.packed2 seq.packed3
  seq.packed4 seq.packed5 seq.packed6}
 let basetype = basetype(type, typedict)
 let elementtype = parameter.basetype
 if elementtype = typeboolean then
  [Local.1, blockitsymbol.seqof.typeint]
 else
  let cat = symbol(tomodref.type, "+", [type, parameter.type], type)
  [Sequence(elementtype, 0)] + Local.1 + forhead(Local.3, [Local.2], basetype)
  + Local.2
  + Local.4
  + deepcopySym.parameter.type
  + cat
  + [Local.3, Lit.1, PlusOp, continue.2]
  + [EndBlock, symbol(internalmod, "checkfornoop", basetype, basetype)]
  + blockitsymbol.basetype
else
 let subflds = flatflds(typedict, type)
 if length.subflds = 1 then
  {only one element in record so type is not represent by actual record} [Local.1]
  + deepcopySym.first.subflds
 else
  for fldno = 1
   , fldkinds = empty:seq.mytype
   , result = empty:seq.symbol
   , fldtype ∈ subflds
  do
   let kind = basetype(fldtype, typedict)
   next(fldno + 1
    , fldkinds + kind
    , result + [Local.1, Lit(fldno - 1), Getfld.kind, deepcopySym.fldtype])
  /for (result + [Record.fldkinds])

function forhead(masteridx:symbol, exitexp:seq.symbol, theseqtype:mytype) seq.symbol
let theseq = Local(value.masteridx + 2)
let totallength = Local(value.masteridx + 3)
[Define.value.theseq] + theseq + GetSeqLength + Define.value.totallength + Lit.1
+ Loopblock([theseqtype, typeint], 2, theseqtype)
+ [masteridx, totallength, GtOp]
+ Br2(1, 2)
+ exitexp
+ Exit
+ theseq
+ masteridx
+ symbol(builtinmod.typeint, "idxNB", theseqtype, typeint, parameter.theseqtype)
+ Define(value.masteridx + 1)

__________________________

type symbolref is toint:int

function symbolref(sym:symbol) symbolref symbolref.addorder.sym

_________________

Function prescan2(s:seq.symdef, typedict:typedict) seq.symdef
{removes name from locals and change length and getseqtype to GetSeqLength and GetSeqType
 }
for acc = empty:seq.symdef, p ∈ s do
 let pdict = 
  for pmap = empty:set.localmap2, parano ∈ arithseq(nopara.sym.p, 1, 1) do
   pmap + localmap2(parano, [Local.parano])
  /for (pmap)
 for nextvar = 1
  , map = pdict
  , result = empty:seq.symbol
  , newdict = typedict
  , sym ∈ code.p
 do
  {if name.module.sym ∈" $define" then next (nextvar+1, localmap2 (value.sym, [Local.nextvar]) ∪ map, result
   +Define.nextvar, newdict) else if name.module.sym ∈" $local" then let l = lookup (map, value.sym) let t
   = value.l_1 next (nextvar, map, result+t, newdict) else if isloopblock.sym then let offset = nextvar-
   firstvar.sym let newmap = for newmap = map, v ∈ arithseq (nopara.sym, 1, firstvar.sym) do localmap2 (v, [Local
   (v+offset)]) ∪ newmap /for (newmap) let newsym = for acc2 = empty:seq.mytype, para ∈ paratypes.sym do acc2
   +basetype (para, newdict) /for (Loopblock (acc2, nextvar, basetype (resulttype.sym, newdict))) next (nextvar+nopara
   .sym, newmap, result+newsym, add (newdict, typebase.firstvar.sym, [resulttype.sym])) else}
  if islocal.sym then
   next(nextvar, map, result + Local.value.sym, newdict)
  else if isdefine.sym then
   next(nextvar, map, result + Define.value.sym, newdict)
  else if isloopblock.sym then
   {???? bug should declare type $base.firstvar.sym type on per EACH function}
   next(nextvar
    , map
    , result + sym
    , add(newdict, typebase.firstvar.sym, [resulttype.sym]))
  else
   next(nextvar
    , map
    , result
    + if isstart.sym then
     Start.basetype(resulttype.sym, newdict)
    else if not.isBuiltin.sym then
     sym
    else if name.sym ∈ "assert" then
     let typ = basetype(para.module.sym, newdict)
     symbol(builtinmod.typ, "assert", seqof.typeword, typ)
    else if name.sym ∈ "length" then
     GetSeqLength
    else if name.sym ∈ "getseqtype" then
     GetSeqType
    else if name.sym ∈ "aborted" then
     symbol(internalmod, "processisaborted", typeptr, typeboolean)
    else
     sym
    , newdict)
 /for (
  {let t = %.result let i = findindex (t," $base"_1) assert i > length.t /or t_(i-1) = dq_1 report
   " SDFFF"+t}
  acc
  + symdef4(sym.p, result, 0, getOptionsBits.p)
 )
/for (acc)

use typedict

use otherseq.symbol 