module postbind

use localmap2

use mytype

use passsymbol

use standard

use symbol

use symboldict

use symref

use typedict

use seq.commoninfo

use seq.findabstractresult

use seq.modref

use set.modref

use otherseq.mytype

use seq.mytype

use set.passsymbols

use encoding.symbol

use seq.symbol

use set.symbol

use seq.symdef

use set.symdef

use otherseq.word

use set.word

use seq.seq.mytype

use seq.encodingpair.symbol

use seq.seq.symbol

use seq.set.symdef

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
  /for(postbindresult(typedict3, symdef(sym.sd, acc) ∪ prg.inline, inline.inline + symdef(sym.sd, acc)))
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
let aa = encoding:seq.encodingpair.symbol
if length.aa = last then
 { assert false report"INLINE"+ for txt ="", sd = toseq.inline do txt + print.sym.sd + print.code.sd + EOL /for(txt)}
 postbindresult(typedict1, result, inline)
else
 for accZ = postbindresult(typedict1, result, inline), pp ∈ subseq(aa, last + 1, length.aa)do
  let symz = data.pp
  if isspecial.symz ∨ isconst.symz ∨ isBuiltin.symz ∨ isGlobal.symz ∨ inModFor.symz then accZ
  else
   let newdict2 = addtype(typedict.accZ, resulttype.symz)
   let lr1 = getCode(source, symz)
   let sd =
    if not.isempty.lr1 ∨ iscompiled(lr1, symz)then symdef(symz, lr1)
    else if istype.symz then symdef(symz, deepcopybody(resulttype.symz, newdict2))
    else if not.isunbound.symz then instantiateTemplate(symz, templates)
    else
     let k2 = lookupbysig(allsyms, symz)
     if isempty.k2 then instantiateTemplate(symz, templates)
     else
      assert cardinality.k2 = 1 report"unbound problem" + print.symz
      let sym2 = k2_1
      if issimple.module.sym2 ∨ iscompiled(getCode(source, sym2), sym2)then
       for paras = empty:seq.symbol, i ∈ arithseq(nopara.sym2, 1, 1)do paras + Local.i /for(symdef(sym2, paras + sym2))
      else instantiateTemplate(sym2, templates)
   let newdict3 = addtypes(newdict2, asset(code.sd + sym.sd))
   {------------}
   let modpara = para.module.sym.sd
   let pdict =
    for pmap = empty:set.localmap2, parano ∈ arithseq(nopara.sym.sd, 1, 1)do pmap + localmap2(parano, [ Local.parano])/for(pmap)
   for cache = empty:set.symdef
   , nextvar = nopara.sym.sd + 1
   , map = pdict
   , result2 = empty:seq.symbol
   , symx ∈ code.sd
   do
    let sym = replaceTsymbol(modpara, symx)
    if name.module.sym ∈ "$define"then
     next(cache, nextvar + 1, localmap2(value.sym, [ Local.nextvar]) ∪ map, result2 + Define.nextvar)
    else if name.module.sym ∈ "$local"then
     let t = value.lookup(map, value.sym)_1
     next(cache, nextvar, map, result2 + t)
    else if isconst.sym then next(cache, nextvar, map, result2 + sym)
    else if name.sym ∈ "primitiveadd" ∧ isBuiltin.sym then
     { let encodingtype = typeref."encoding encoding stdlib"}
     let encodingstatetype = typeref."encodingstate encoding stdlib"
     let encodingpairtype = typeref."encodingpair encoding stdlib"
     let addefunc =
      symbol(moduleref("stdlib encoding", para.module.sym)
      ,"add"
      , [ addabstract(encodingstatetype, para.module.sym)
      , addabstract(encodingpairtype, para.module.sym)
      ]
      , addabstract(encodingstatetype, para.module.sym)
      )
     let add2 = symbol(internalmod,"addencoding", [ typeint, typeptr, typeint, typeint], typeint)
     let dc = deepcopySym.addabstract(encodingpairtype, para.module.sym)
     let discard = symbolref.addefunc
     let discard2 = symbolref.dc
     let discard3 = symbolref.add2
     next(cache, nextvar + 1, map, result2 + [ PreFref, addefunc, PreFref, dc, add2])
    else if name.sym ∈ "getinstance" ∧ isBuiltin.sym then
     let get = symbol(internalmod,"getinstance", typeint, typeptr)
     let typ = para.module.sym
     let gl =
      symbol4(moduleref."internallib $global"
      ,"global"_1
      , typ
      , empty:seq.mytype
      , seqof.typeint
      )
     let encodenocode =
      if typ = typeref."typename tausupport stdlib"then [ Lit.2]
      else if typ = seqof.typechar then [ Lit.1]
      else
       let encodenosym = symbol(modTausupport,"encodingno", seqof.typeword, typeint)
       let discard = symbolref.encodenosym
       ifthenelse([ gl, Lit.0, Getfld.typeint, Define.nextvar, Local.nextvar, Lit.0, EqOp]
       , [ gl, Words.fullprint.typ, encodenosym, setSym.typeint, Define(nextvar + 1), gl, Lit.0, Getfld.typeint]
       , [ Local.nextvar]
       , typeint
       )
     next(cache, nextvar + 2, map, result2 + encodenocode + get)
    else if name.sym ∈ "pushflds" ∧ isBuiltin.sym then
     next(cache
     , nextvar
     , map
     , if iscoretype.para.module.sym then result2
     else
      let t = flatflds(newdict3, para.module.sym)
      if isempty.t ∨ typeT ∈ t then result2 + sym
      else if length.t = 1 then result2
      else
       for newresult = result2 >> 1, idx = 0, x ∈ t do next(newresult + [ last.result2, Lit.idx, Getfld.x], idx + 1)/for(newresult)
     )
    else if not.isempty.result2 ∧ last.result2 = PreFref then
     next(cache, nextvar, map, result2 + test(symx, newdict3, modpara, empty:set.symdef))
    else
     let cacheValue = lookup(cache, symdef(symx, empty:seq.symbol))
     if not.isempty.cacheValue then next(cache, nextvar, map, result2 + code.cacheValue_1)
     else
      let newValue = test(symx, newdict3, modpara, inline.accZ)
      next(cache + symdef(symx, newValue), nextvar, map, result2 + newValue)
   /for(postbindresult(newdict3
   , symdef(symz, result2) ∪ prg.accZ
   , if verysimpleinline(symz, result2)then inline.accZ + symdef(symz, result2)else inline.accZ
   ))
 /for(usedsyms(allsyms, source, length.aa, prg.accZ, templates, typedict.accZ, inline.accZ))

function test(symx:symbol, newdict3:typedict, modpara:mytype, inline:set.symdef)seq.symbol
let sym = replaceTsymbol(modpara, symx)
if isspecial.sym then
 if isSequence.sym then [ Sequence(parameter.basetype(resulttype.sym, newdict3), nopara.sym)]
 else if isstart.sym then [ Start.basetype(resulttype.sym, newdict3)]else [ sym]
else if isInternal.sym then
 let discard = symbolref.sym
 [ sym]
else if not.isBuiltin.sym then
 let xx = getCode(inline, sym)
 if isempty.xx then
  let discard = symbolref.sym
  [ sym]
 else xx << nopara.sym
else if name.sym ∈ "bitcast"then
 let a = coretype(first.paratypes.sym, newdict3)
 let b = coretype(resulttype.sym, newdict3)
 if a = b then empty:seq.symbol else [ symbol(internalmod,"bitcast", a, b)]
else if name.sym ∈ "processresult"then [ Lit.2, Getfld.coretype(para.module.sym, newdict3)]
else
 [ if name.sym ∈ "buildrecord"then
  let t = flatflds(newdict3, para.module.sym)
  if isempty.t ∨ typeT ∈ t then sym else Record.t
 else if name.sym ∈ "typesize"then
  let typ = para.module.sym
  if typ = typeint ∨ typ = typereal ∨ typ = typeptr ∨ isseq.typ then Lit.1
  else
   let t = flatflds(newdict3, typ)
   if isempty.t ∨ typeT ∈ t then sym else Lit.length.t
 else if name.sym ∈ "length"then GetSeqLength
 else if name.sym ∈ "packed"then
  let typ = seqof.coretype(para.module.sym, newdict3)
  let tmp = symbol(modTausupport,"blockIt", typ, typ)
  let discard = symbolref.tmp
  tmp
 else if name.sym ∈ "aborted"then
  symbol(internalmod,"processisaborted", typeptr, typeboolean)
 else if name.sym ∈ "assert"then abortsymbol.coretype(para.module.sym, newdict3)
 else if name.sym ∈ "_"then
  let seqtype = basetype(first.paratypes.sym, newdict3)
  symbol(internalmod,"indexseq45", seqtype, typeint, parameter.seqtype)
 else if name.sym ∈ "getseqtype"then GetSeqType
 else if name.sym ∈ "set"then setSym.coretype(para.module.sym, newdict3)
 else if name.sym = "forexp"_1 then
  let paras =
   for acc = empty:seq.mytype, p ∈ paratypes.sym do
    acc + if"$base"_1 ∈ print.p then p else basetype(p, newdict3)
   /for(acc)
  symbol(moduleref."internallib builtin","forexp", paras, last.paras)
 else if name.sym = "createthreadY"_1 then
  let paras =
   for paras = empty:seq.mytype, p ∈ paratypes.sym do paras + coretype(p, newdict3)/for(paras)
  let rt = processof.coretype(parameter.resulttype.sym, newdict3)
  symbol(builtinmod.rt,"createthreadY", paras, typeptr)
 else if name.sym ∈ "fld getfld"then
  let typ = resulttype.sym
  if iscoretype.typ then Getfld.typ
  else if isabstract.typ then sym
  else
   let a = flatflds(newdict3, typ)
   assert not.isempty.a report"cannot find type getfld" + print.typ
   if length.a > 1 then symbol(internalmod,"GEP", seqof.typeptr, typeint, typeptr)
   else Getfld.first.a
 else if name.sym ∈ "empty"then Sequence(coretype(para.module.sym, newdict3), 0)
 else
  assert name.sym ∈ "xoffsets xbuild"report"post bind error:" + print.sym
  sym
 ]

function instantiateTemplate(sym2:symbol, templates:set.symdef)symdef
if issimple.module.sym2 then symdef(sym2, empty:seq.symbol)
else
 let gx = findabstract(templates, sym2)
 assert length.gx = 1 report"Cannot find template for X" + print.length.gx + print.sym2
 for newcode = empty:seq.symbol, sym4 ∈ code.sd.gx_1 do newcode + replaceTsymbol(modpara.gx_1, sym4)/for(symdef(sym2, newcode))

function iscoretype(typ:mytype)boolean
typ = typeint ∨ typ = typereal ∨ typ = typeptr ∨ typ = typeboolean ∨ isseq.typ ∨ isencoding.typ

function deepcopybody(type:mytype, typedict:typedict)seq.symbol
if type = typeint ∨ type = typeword ∨ isencoding.type then [ Local.1]
else if isseq.type then
 { base types are int real boolean ptr seq.int seq.real seq.boolean seq.ptr seq.byte seq.bit seq.packed2 seq.packed3 seq 
.packed4 seq.packed5 seq.packed6 or $base.x where x is a integer }
 let basetype = basetype(type, typedict)
 let elementtype = parameter.basetype
 if elementtype = typebyte ∨ elementtype = typebit ∨ elementtype = typeboolean then
  [ Local.1, symbol(modTausupport,"blockIt", seqof.typeint, seqof.typeint)]
 else
  let cat = symbol(tomodref.type,"+", [ type, parameter.type], type)
  let resulttype = basetype
  let element =
   symbol(moduleref("internallib $for", elementtype)
   ,"element"
   , empty:seq.mytype
   , elementtype
   )
  let acc =
   symbol(moduleref("internallib $for", typeptr),"acc", empty:seq.mytype, typeptr)
  [ Sequence(elementtype, 0)]
  + [ Local.1
  , acc
  , element
  , acc
  , element
  , deepcopySym.parameter.type
  , cat
  , Littrue
  , acc
  , symbol(builtinmod.typeint
  ,"forexp"
  , [ resulttype, resulttype, resulttype, elementtype, typeptr, typeboolean, resulttype]
  , resulttype
  )
  ]
  + symbol(modTausupport,"blockIt", basetype, basetype)
else
 let subflds = flatflds(typedict, type)
 if length.subflds = 1 then
  { only one element in record so type is not represent by actual record } [ Local.1]
  + deepcopySym.first.subflds
 else
  for fldno = 1, fldkinds = empty:seq.mytype, result = empty:seq.symbol, fldtype ∈ subflds do
   let kind = basetype(fldtype, typedict)
   next(fldno + 1, fldkinds + kind, result + [ Local.1, Lit(fldno - 1), Getfld.kind, deepcopySym.fldtype])
  /for(result + [ Record.fldkinds])

Module localmap2

use standard

use symbol

use hashset.localmap2

use seq.localmap2

use set.localmap2

use seq.symbol

type localmap2 is key:int, value:seq.symbol

Export type:localmap2

Export type:hashset.localmap2

Export localmap2(key:int, value:seq.symbol)localmap2

Export key(localmap2)int

Export value(localmap2)seq.symbol

Export empty:set.localmap2 set.localmap2

Export isempty(set.localmap2)boolean

Export_(set.localmap2, int)localmap2

Export +(set.localmap2, localmap2)set.localmap2

Export ∪(localmap2, set.localmap2)set.localmap2

Function lookup(a:set.localmap2, key:int)set.localmap2 lookup(a, localmap2(key, empty:seq.symbol))

Function =(a:localmap2, b:localmap2)boolean key.a = key.b

Function hash(a:localmap2)int hash.key.a

Function ?(a:localmap2, b:localmap2)ordering key.a ? key.b

Export empty:hashset.localmap2 hashset.localmap2

Export isempty(seq.localmap2)boolean

Export_(seq.localmap2, int)localmap2

Export +(hashset.localmap2, localmap2)hashset.localmap2

Export ∪(localmap2, hashset.localmap2)hashset.localmap2

Function lookup(a:hashset.localmap2, key:int)seq.localmap2 lookup(a, localmap2(key, empty:seq.symbol))

Module hashset.T

use bits

use standard

use seq.T

use seq.hashelement.T

use otherseq.seq.hashelement.T

use seq.seq.hashelement.T

type hashelement is data:T, hash:int

type hashset is cardinality:int, table:seq.seq.hashelement.T

Export type:hashset.T

Export type:hashelement.T

Export type:seq.seq.hashelement.T

Export cardinality(hashset.T)int

Function empty:hashset.T hashset.T
let x = empty:seq.hashelement.T
hashset(0, [ x, x, x, x])

unbound =(a:T, b:T)boolean

unbound hash(T)int

Function lookup(s:hashset.T, ele:T)seq.T
let h = hash.ele
for acc = empty:seq.T, e ∈(table.s)_(h mod length.table.s + 1)do if data.e = ele then acc + data.e else acc /for(acc)

Function toseq(h:hashset.T)seq.T
let tablesize = length.table.h
let mask = bits.-1 >> (65 - floorlog2.tablesize)
for acc = empty:seq.T, idx ∈ arithseq(tablesize, 1, 1)do
 for acc2 = acc, e ∈(table.h)_idx do if(bits.hash.e ∧ mask) = bits(idx - 1)then acc2 + data.e else acc2 /for(acc2)
/for(acc)

function notsamehash(ele:T, a:int, b:int, mask:bits)boolean(bits.a ∧ mask) ≠ (bits.b ∧ mask)

Function +(h:hashset.T, ele:T)hashset.T
let tablesize = length.table.h
let mask = bits.-1 >> (65 - floorlog2.tablesize)
let hash = hash.ele
let dataindex = toint(tobits.hash ∧ mask) + 1
for acc = empty:seq.hashelement.T, found = false, e ∈(table.h)_dataindex do
 if data.e = ele then next(acc + e, true)
 else if notsamehash(ele, hash, hash.e, mask)then next(acc, found)else next(acc + e, found)
/for(let t =
 replace(table.h, dataindex, if found then acc else [ hashelement(ele, hash)] + acc)
hashset(if found then cardinality.h else cardinality.h + 1
, if 3 * cardinality.h > 2 * tablesize then t + t + t + t else t
))

Function ∪(ele:T, h:hashset.T)hashset.T replace(h, hashelement(ele, hash.ele))

function replace(h:hashset.T, ele:hashelement.T)hashset.T
let tablesize = length.table.h
let mask = bits.-1 >> (65 - floorlog2.tablesize)
let hash = hash.ele
let dataindex = toint(tobits.hash ∧ mask) + 1
for acc = [ ele], found = false, e ∈(table.h)_dataindex do
 if data.e = data.ele then next(acc, true)
 else if notsamehash(data.ele, hash, hash.e, mask)then next(acc, found)else next(acc + e, found)
/for(let t = replace(table.h, dataindex, acc)
hashset(if found then cardinality.h else cardinality.h + 1
, if 3 * cardinality.h > 2 * tablesize then t + t + t + t else t
)) 