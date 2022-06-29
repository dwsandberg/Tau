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

use symboldict

use set.symdef

use typedict

function verysimpleinline(sym1:symbol, code:seq.symbol)boolean
if isempty.code ∨ last.code = Optionsym ∨ length.code > 10 then false
else
 let nopara = nopara.sym1
 for isverysimple = length.code ≥ nopara, idx = 1, sym ∈ code
 while isverysimple
 do if idx ≤ nopara then next(sym = Local.idx, idx + 1)
 else
  next(if isconst.sym then true
  else if isBuiltin.sym then name.sym ∈ "fld getfld length getseqlength"
  else if isInternal.sym then name.sym ∉ "indexseq45"
  else not.isbr.sym ∧ not.isdefine.sym ∧ not.islocal.sym
  , idx + 1
  )
 /for(isverysimple ∧ name.sym1 ∉ "decodeword encodeword")

type postbindresult is typedict:typedict, prg:set.symdef, inline:set.symdef

Export typedict(postbindresult)typedict

Export prg(postbindresult)set.symdef

Function postbind(roots:seq.symbol, theprg:set.symdef, templates:set.symdef, typedict1:typedict)postbindresult
let discard = for acc = symbolref.Lit.0, r ∈ roots do symbolref.r /for(0)
for inline = postbindresult(typedict1, theprg, empty:set.symdef)
, allsyms = empty:set.symbol
, sd ∈ toseq.theprg
do
 next(if not.isabstract.module.sym.sd ∧ verysimpleinline(sym.sd, code.sd)then
  for acc = empty:seq.symbol, typedict3 = typedict.inline, symx ∈ code.sd do
   if islocal.symx ∨ isconst.symx then next(acc + symx, typedict3)
   else
    let newdict3 = addtypes(typedict3, asset(code.sd + sym.sd))
    next(acc + test(symx, newdict3, para.module.sym.sd, empty:set.symdef), newdict3)
  /for(postbindresult(typedict3
  , symdef(sym.sd, acc, paragraphno.sd) ∪ prg.inline
  , inline.inline + symdef(sym.sd, acc, paragraphno.sd)
  ))
 else inline
 , allsyms + sym.sd
 )
/for(usedsyms(symboldict(allsyms, empty:seq.commoninfo)
, prg.inline
, 0
, empty:set.symdef
, templates
, typedict.inline
, inline.inline
))

function usedsyms(allsyms:symboldict
, source:set.symdef
, last:int
, result:set.symdef
, templates:set.symdef
, typedict1:typedict
, inline:set.symdef
)postbindresult
let aa = encodingdata:symbol
if length.aa = last then
 {assert false report"INLINE"+for txt="", sd=toseq.inline do txt+print.sym.sd+print.code.sd+EOL /for(txt)}
 postbindresult(typedict1, result, inline)
else
 for accZ = postbindresult(typedict1, result, inline), symz ∈ subseq(aa, last + 1, length.aa)do
  if isspecial.symz ∨ isconst.symz ∨ isBuiltin.symz ∨ isGlobal.symz ∨ inModFor.symz then accZ
  else
   let newdict2 = addtype(typedict.accZ, resulttype.symz)
   let b = getSymdef(source, symz)
   let sd = 
    if not.isempty.b then b_1
    else if istype.symz then symdef(symz, deepcopybody(resulttype.symz, newdict2), 0)
    else
     {assert name.symz /nin"hash"report"ZZ"+print.symz+print.lookupbysig(allsyms, symz)_1}
     {if not.isunbound.symz then instantiateTemplate(symz, templates)else}
     let k21 = lookupbysig(allsyms, symz)
     let k2 = 
      if cardinality.k21 < 2 then k21
      else
       for acc = empty:set.symbol, sy ∈ toseq.k21 do if isunbound.sy then acc else acc + sy /for(if isempty.acc then k21 else acc /if)
     if isempty.k2 then instantiateTemplate(symz, templates)
     else
      assert cardinality.k2 = 1
      report"unbound problem" + print.symz
      + if cardinality.k2 > 1 then
       for txt = "", symt ∈ toseq.k2 do
        txt + if isunbound.symt then"T"else"F"/if
        + library.module.symt
        + print.symt
       /for(txt)
      else""
      let sym2 = k2_1
      let b2 = getSymdef(source, sym2)
      if not.isempty.b2 then
       for paras = empty:seq.symbol, i ∈ arithseq(nopara.sym2, 1, 1)do paras + Local.i /for(symdef(sym2, paras + sym2, paragraphno.b2_1))
      else instantiateTemplate(sym2, templates)
   let newdict3 = addtypes(newdict2, asset(code.sd + sym.sd))
   {------------}
   let modpara = para.module.sym.sd
   let pdict = 
    for pmap = empty:set.localmap2, parano ∈ arithseq(nopara.sym.sd, 1, 1)do pmap + localmap2(parano, [Local.parano])/for(pmap)
   for cache = empty:set.symdef
   , nextvar = nopara.sym.sd + 1
   , map = pdict
   , result2 = empty:seq.symbol
   , symx ∈ code.sd
   do
    let sym = replaceTsymbol(modpara, symx)
    if name.module.sym ∈ "$define"then
     next(cache, nextvar + 1, localmap2(value.sym, [Local.nextvar]) ∪ map, result2 + Define.nextvar)
    else if name.module.sym ∈ "$local"then
     let t = value.lookup(map, value.sym)_1
     next(cache, nextvar, map, result2 + t)
    else if isconst.sym then next(cache, nextvar, map, result2 + sym)
    else if name.sym ∈ "primitiveadd" ∧ isBuiltin.sym then
     let T = para.module.sym
     let encodingstatetype = typeref."encodingstate encoding"
     if true then
      let encodingpairtype = typeref."encodingpair encoding"
      let addefunc = 
       symbol(moduleref("encoding", T)
       , "add"
       , [addabstract(encodingstatetype, T), addabstract(encodingpairtype, T)]
       , addabstract(encodingstatetype, T)
       )
      let add2 = symbol(internalmod, "addencoding", [typeint, typeptr, typeint, typeint], typeint)
      let dc = deepcopySym.addabstract(encodingpairtype, T)
      let discard = symbolref.addefunc
      let discard2 = symbolref.dc
      let discard3 = symbolref.add2
      next(cache, nextvar + 1, map, result2 + [PreFref, addefunc, PreFref, dc, add2])
     else
      let addefunc = 
       symbol(moduleref("encoding", T)
       , "add"
       , [addabstract(encodingstatetype, T), T]
       , addabstract(encodingstatetype, T)
       )
      let add2 = symbol(internalmod, "addencoding", [typeint, typeptr, typeint, typeint], typeint)
      let dc = deepcopySym.T
      let discard = symbolref.addefunc
      let discard2 = symbolref.dc
      let discard3 = symbolref.add2
      next(cache, nextvar + 1, map, result2 + [PreFref, addefunc, PreFref, dc, add2])
    else if name.sym ∈ "getinstance" ∧ isBuiltin.sym then
     let get = symbol(internalmod, "getinstance", typeint, typeptr)
     let typ = para.module.sym
     let gl = 
      symbol4(moduleref."internallib $global"
      , "global"_1
      , typ
      , empty:seq.mytype
      , seqof.typeint
      )
     let encodenocode = 
      if typ = typeref."typename tausupport"then[Lit.2]
      else if typ = seqof.typechar then[Lit.1]
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
       , Getfld.typeint
       ]
       , [Local.nextvar]
       , typeint
       )
     next(cache, nextvar + 2, map, result2 + encodenocode + get)
    else if name.sym ∈ "pushflds" ∧ isBuiltin.sym then
     let typ = para.module.sym
     next(cache
     , nextvar
     , map
     , if iscore4.typ ∨ isseq.typ ∨ isencoding.typ then result2
     else
      let t = flatflds(newdict3, typ)
      if isempty.t ∨ typeT ∈ t then result2 + sym
      else if length.t = 1 then result2
      else
       for newresult = result2 >> 1, idx = 0, x ∈ t do next(newresult + [last.result2, Lit.idx, Getfld.x], idx + 1)/for(newresult)
     )
    else if not.isempty.result2 ∧ last.result2 = PreFref then
     next(cache, nextvar, map, result2 + test(symx, newdict3, modpara, empty:set.symdef))
    else
     let cacheValue = getSymdef(cache, symx)
     if not.isempty.cacheValue then next(cache, nextvar, map, result2 + code.cacheValue_1)
     else
      let newValue = test(symx, newdict3, modpara, inline.accZ)
      next(cache + symdef(symx, newValue, 0), nextvar, map, result2 + newValue)
   /for(postbindresult(newdict3
   , symdef(symz, result2, 0) ∪ prg.accZ
   , if verysimpleinline(symz, result2)then inline.accZ + symdef(symz, result2, 0)else inline.accZ
   ))
 /for(usedsyms(allsyms, source, length.aa, prg.accZ, templates, typedict.accZ, inline.accZ))

function test(symx:symbol, newdict3:typedict, modpara:mytype, inline:set.symdef)seq.symbol
let sym = replaceTsymbol(modpara, symx)
if isspecial.sym then
 if isSequence.sym then[Sequence(parameter.basetype(resulttype.sym, newdict3), nopara.sym)]
 else if isstart.sym then[Start.basetype(resulttype.sym, newdict3)]else[sym]
else if isInternal.sym then
 let discard = symbolref.sym
 [sym]
else if not.isBuiltin.sym then
 let xx = getCode(inline, sym)
 if isempty.xx then
  let discard = symbolref.sym
  [sym]
 else xx << nopara.sym
else if name.sym ∈ "bitcast toptr"then
 let a = basetype(first.paratypes.sym, newdict3)
 let b = basetype(resulttype.sym, newdict3)
 if if isseq.a then typeptr else a /if
 = if isseq.b then typeptr else b then
  empty:seq.symbol
 else[symbol(internalmod, "bitcast", a, b)]
else if name.sym ∈ "processresult"then[Lit.2, Getfld.basetype(para.module.sym, newdict3)]
else if name.sym ∈ "typestructure"then
 let roottype = para.module.sym
 let tmp = 
  for acc = empty:seq.seq.mytype, row ∈ asseqseqmytype.subdict(newdict3, roottype)do
   if first.row = roottype then[row] + acc else acc + row
  /for(acc)
 {root type is now first row in tmp}
 for acc = empty:seq.symbol, row ∈ tmp do
  acc
  + for accrow = empty:seq.symbol, t ∈ row do
   let fp = fullprint.t
   accrow
   + for acctype = empty:seq.symbol, idx = 1, w ∈ fp do
    next(acctype
    + if idx < 3 then[Word.w]else[Word.w, Record.[typeword, typeword, typeword]]
    , if idx = 3 then 1 else idx + 1
    )
   /for(acctype + Sequence(typeword, length.fp / 3))
  /for(accrow + Sequence(seqof.typeptr, length.row))
 /for(acc + Sequence(typeptr, length.tmp))
else
 [if name.sym ∈ "buildrecord"then
  let t = flatflds(newdict3, para.module.sym)
  if isempty.t ∨ typeT ∈ t then sym else Record.t
 else if name.sym ∈ "typesize"then
  let typ = para.module.sym
  if iscore4.typ ∨ isseq.typ then Lit.1
  else
   let t = flatflds(newdict3, typ)
   if isempty.t ∨ typeT ∈ t then sym else Lit.length.t
 else if name.sym ∈ "length"then GetSeqLength
 else if name.sym ∈ "packed"then
  let typ = basetype(seqof.para.module.sym, newdict3)
  let tmp = blockitsymbol.typ
  let discard = symbolref.tmp
  tmp
 else if name.sym ∈ "aborted"then
  symbol(internalmod, "processisaborted", typeptr, typeboolean)
 else if name.sym ∈ "assert"then abortsymbol.basetype(para.module.sym, newdict3)
 else if name.sym ∈ "_"then
  let seqtype = basetype(first.paratypes.sym, newdict3)
  symbol(internalmod, "indexseq45", seqtype, typeint, parameter.seqtype)
 else if name.sym ∈ "getseqtype"then GetSeqType
 else if name.sym ∈ "set"then setSym.basetype(para.module.sym, newdict3)
 else if name.sym = "forexp"_1 then
  let paras = 
   for acc = empty:seq.mytype, p ∈ paratypes.sym do
    acc + if"$base"_1 ∈ print.p then p else basetype(p, newdict3)
   /for(acc)
  symbol(moduleref."internallib builtin", "forexp", paras, last.paras)
 else if name.sym = "createthreadY"_1 then
  let paras = 
   for paras = empty:seq.mytype, p ∈ paratypes.sym do
    let tmp = basetype(p, newdict3)
    paras + if isseq.tmp then typeptr else tmp
   /for(paras)
  let rt = basetype(parameter.resulttype.sym, newdict3)
  symbol(builtinmod.processof.if isseq.rt then typeptr else rt
  , "createthreadY"
  , paras
  , typeptr
  )
 else if name.sym ∈ "fld getfld"then
  let typ = resulttype.sym
  if iscore4.typ ∨ isseq.typ ∨ isencoding.typ then Getfld.typ
  else if isabstract.typ then sym
  else
   let a = flatflds(newdict3, typ)
   assert not.isempty.a report"cannot find type getfld" + print.typ
   if length.a > 1 then symbol(internalmod, "GEP", seqof.typeptr, typeint, typeptr)
   else Getfld.first.a
 else if name.sym ∈ "empty"then Sequence(basetype(para.module.sym, newdict3), 0)
 else
  assert name.sym ∈ "xoffsets xbuild"report"post bind error:" + print.sym
  sym
 ]

function instantiateTemplate(sym2:symbol, templates:set.symdef)symdef
if issimple.module.sym2 then symdef(sym2, empty:seq.symbol, 0)
else
 let gx = findabstract(templates, sym2)
 assert length.gx = 1
 report"Cannot find template for X" + %.length.gx + print.sym2
 + if isempty.gx then""
 else
  for txt = "", k ∈ gx do txt + EOL + print.sym.sd.k + print.modpara.k /for(txt)
 for newcode = empty:seq.symbol, sym4 ∈ code.sd.gx_1 do newcode + replaceTsymbol(modpara.gx_1, sym4)/for(symdef(sym2, newcode, 0))

function deepcopybody(type:mytype, typedict:typedict)seq.symbol
if type = typeint ∨ type = typeword ∨ isencoding.type then[Local.1]
else if isseq.type then
 {base types are int real boolean ptr seq.int seq.real seq.boolean seq.ptr seq.byte seq.bit seq.packed2 seq.packed3 seq 
.packed4 seq.packed5 seq.packed6 or $base.x where x is a integer}
 let basetype = basetype(type, typedict)
 let elementtype = parameter.basetype
 if elementtype = typebit ∨ elementtype = typeboolean then[Local.1, blockitsymbol.seqof.typeint]
 else
  let cat = symbol(tomodref.type, "+", [type, parameter.type], type)
  let resulttype = basetype
  let element = 
   symbol(moduleref("internallib $for", elementtype)
   , "element"
   , empty:seq.mytype
   , elementtype
   )
  let acc = 
   symbol(moduleref("internallib $for", typeptr), "acc", empty:seq.mytype, typeptr)
  [Sequence(elementtype, 0)]
  + [Local.1
  , acc
  , element
  , acc
  , element
  , deepcopySym.parameter.type
  , cat
  , Littrue
  , acc
  , symbol(builtinmod.typeint
  , "forexp"
  , [resulttype, resulttype, resulttype, elementtype, typeptr, typeboolean, resulttype]
  , resulttype
  )
  ]
  + blockitsymbol.basetype
else
 let subflds = flatflds(typedict, type)
 if length.subflds = 1 then
  {only one element in record so type is not represent by actual record}[Local.1]
  + deepcopySym.first.subflds
 else
  for fldno = 1, fldkinds = empty:seq.mytype, result = empty:seq.symbol, fldtype ∈ subflds do
   let kind = basetype(fldtype, typedict)
   next(fldno + 1, fldkinds + kind, result + [Local.1, Lit(fldno - 1), Getfld.kind, deepcopySym.fldtype])
  /for(result + [Record.fldkinds])

__________________________

type symbolref is toint:int

function symbolref(sym:symbol)symbolref symbolref.addorder.sym 