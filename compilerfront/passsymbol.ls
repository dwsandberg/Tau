Module passsymbol

use seq.findabstractresult

use set.modref

use mytype

use seq.mytype

use seq.seq.mytype

use set.mytype

use set.passsymbols

use set.passtypes

use standard

use seq.symbol

use set.symbol

use symbol1

use symbolMode

use symboldict

use seq.symdef

use process.seq.symdef

use set.symdef

Export type:findabstractresult

Export modpara(findabstractresult) mytype

Export sd(findabstractresult) symdef

Export type:partdict

Export req(partdict) set.symdef

Export syms(partdict) set.symbol

Export type:passsymbols

Export defines(passsymbols) set.symbol

Export exports(passsymbols) set.symbol

Export modname(passsymbols) modref

Export srclink(passsymbols) seq.symdef

Export typedict(passsymbols) set.mytype

Export uses(passsymbols) set.modref

Export passsymbols(
modname:modref
, uses:set.modref
, defines:set.symbol
, exports:set.symbol
, unresolvedexports:set.symbol
, typedict:set.mytype
, text:seq.symdef
) passsymbols

Export type:prg6

Export abstract(prg6) seq.passsymbols

Export code(prg6) set.symdef

Export modules(prg6) set.passsymbols

Export simple(prg6) seq.passsymbols

Export types(prg6) seq.seq.mytype

Export type:symdef {From symbol} {From symbolconstant}

Export code(symdef) seq.symbol {From symbol} {From symbolconstant}

Export sym(symdef) symbol {From symbol} {From symbolconstant}

Export symdef(symbol, seq.symbol, int) symdef {From symbol} {From symbolconstant}

Function resolvesymbols(
allsrc:seq.seq.word
, lib:word
, mods:set.passtypes
, libmods:set.passsymbols
) prg6
let passtypes = mods
for
 typeflds = empty:seq.seq.mytype
 , paragraphno = 1
 , text = empty:seq.symdef
 , modlist = libmods
 , defines = empty:seq.symbol
 , exports = empty:set.symbol
 , unresolvedexports = empty:set.symbol
 , uses = empty:set.modref
 , accmodname = internalmod
 , acctypes = empty:set.mytype
 , typearcs = empty:seq.symdef
 , m ∈ allsrc
do
 let input = m,
 if isempty.input then
  next(
   typeflds
   , paragraphno + 1
   , text
   , modlist
   , defines
   , exports
   , unresolvedexports
   , uses
   , accmodname
   , acctypes
   , typearcs
  )
 else if input sub 1 ∈ "Module module" then
  let x = findpasstypes(passtypes, lib, input)
  assert not.isempty.x report "did not find:(input)",
  let lastpass =
   resolve(
    empty:set.passsymbols
    , passsymbols(accmodname, uses, asset.defines, exports, unresolvedexports, acctypes, text)
    , allsrc
   ),
  next(
   typeflds
   , paragraphno + 1
   , empty:seq.symdef
   , modlist + lastpass
   , empty:seq.symbol
   , empty:set.symbol
   , empty:set.symbol
   , uses.x sub 1
   , modname.x sub 1
   , formtypedict(passtypes, x sub 1)
   , typearcs
  )
 else if input sub 1 ∈ "Function function Builtin builtin Export unbound" then
  let input0 =
   if subseq(input, 1, 3) = "Export type:" then
    let x1 = findindex(input, "{" sub 1)
    let xtype = if x1 > n.input then input << 3 else subseq(input, 4, x1 - 1),
    "Export type::(xtype) (:(xtype)):(xtype)"
   else input
  let b = symbolparse(input0, acctypes, accmodname)
  let modname =
   if input sub 1 ∈ "Builtin builtin" then if isSimple.accmodname then internalmod else accmodname
   else accmodname
  let sym =
   if n.text.b = 1 then
    let name = text.b,
    if name = "true" then Littrue
    else if name = "false" then Litfalse
    else symbol(modname, text.b, types.b >> 1, (types.b) sub n.types.b)
   else
    symbol4(
     modname
     , (text.b) sub 1
     , (types.b) sub 1
     , subseq(types.b, 2, n.types.b - 1)
     , (types.b) sub n.types.b
    ),
  assert checkwellformed.sym report "Must use type T in function name or parameters in parameterized module and T cannot be used in non-parameterized module:(input)",
  if input sub 1 = "unbound" sub 1 then
   next(
    typeflds
    , paragraphno + 1
    , text
    , modlist
    , defines + setunbound.sym
    , exports
    , unresolvedexports
    , uses
    , accmodname
    , acctypes
    , typearcs
   )
  else if input sub 1 = "Export" sub 1 then
   next(
    typeflds
    , paragraphno + 1
    , if "OPTION" sub 1 ∈ input then text + symdef(sym, empty:seq.symbol, paragraphno)
    else text
    , modlist
    , defines
    , exports
    , unresolvedexports + sym
    , uses
    , accmodname
    , acctypes
    , typearcs
   )
  else
   assert sym ∉ defines report "Function" + wordname.sym + "is defined twice in module" + %.modname,
   next(
    typeflds
    , paragraphno + 1
    , text + symdef(sym, empty:seq.symbol, paragraphno)
    , modlist
    , defines + sym
    , if input sub 1 ∈ "Function Builtin" then exports + sym else exports
    , unresolvedexports
    , uses
    , accmodname
    , acctypes
    , typearcs
   )
 else if input sub 1 ∈ "type" then
  let b = symbolparse(input, acctypes + typeseqdec, accmodname)
  let typs = types.b
  assert ":" sub 1 ∉ text.b ∨ subseq(input, 4, 4) = "sequence" report
   "<* literal In module:(accmodname) name of field is missing in: *>
   /br:(input)"
  let typesym = {deepcopy is used to represent type} deepcopySym.typs sub 1
  let isseq = typs sub 2 = typeseqdec
  let flds = flds(isseq, text.b, accmodname, input sub 2, typs)
  let newdefines =
   for acc = defines + typesym, sd ∈ flds do acc + sym.sd,
   acc,
  let tt = if isseq then [typs sub 1, typeint, typeint] + typs << 2 else typs,
  next(
   typeflds + tt
   , paragraphno + 1
   , text
   , modlist
   , newdefines
   , exports
   , unresolvedexports
   , uses
   , accmodname
   , acctypes
   , typearcs + flds
  )
 else
  next(
   typeflds
   , paragraphno + 1
   , text
   , modlist
   , defines
   , exports
   , unresolvedexports
   , uses
   , accmodname
   , acctypes
   , typearcs
  )
let lastpass =
 resolve(
  empty:set.passsymbols
  , passsymbols(accmodname, uses, asset.defines, exports, unresolvedexports, acctypes, text)
  , allsrc
 )
let allmods = resolveexports(modlist + lastpass, 100000, allsrc)
for abstract = empty:seq.passsymbols, simple = empty:seq.passsymbols, m2 ∈ toseq.allmods
do
 if isAbstract.modname.m2 then next(abstract + m2, simple)
 else next(abstract, simple + m2),
prg6(asset.typearcs, allmods, typeflds, simple, abstract)

type prg6 is
code:set.symdef
, modules:set.passsymbols
, types:seq.seq.mytype
, simple:seq.passsymbols
, abstract:seq.passsymbols

Function flds(
isseq:boolean
, binfotext:seq.word
, modname:modref
, name:word
, typs:seq.mytype
) seq.symdef
let recordtype = if isSimple.modname then typs sub 1 else addabstract(typs sub 1, typeT),
if not.isseq ∧ n.typs = 2 then
 let typ = recordtype,
 if iscore4.typ then empty:seq.symdef
 else
  let fldtype = typs sub n.typs,
  [
   symdef(symbol(modname, [name], [fldtype], typ), [Local.1], 0)
   , symdef(symbol(modname, binfotext, [typ], fldtype), [Local.1], 0)
  ]
else
 let indexfunc =
  if isseq then symbol(modname, "sequenceIndex", [recordtype, typeint], typeT)
  else Lit.0
 for
  flds = empty:seq.symdef
  , idx = 1
  , knownsize = if isseq then 1 else 0
  , unknownsize = empty:seq.symbol
  , constructflds = if isseq then [Fref.indexfunc, Local.1] else empty:seq.symbol
  , fldtype ∈ if isseq then [typeint] + typs << 2 else typs << 1
 do
  let size = knownsize.fldtype
  let usize =
   if size = 1 then unknownsize
   else unknownsize + symbol(builtinmod.fldtype, "typesize", typeint) + PlusOp,
  if binfotext sub idx ∈ ":" then next(flds, idx + 1, knownsize + size, usize, constructflds)
  else
   next(
    flds + fldsym(modname, binfotext sub idx, recordtype, fldtype, knownsize, unknownsize)
    , idx + 1
    , knownsize + size
    , usize
    , constructflds
     + (if fldtype = typeint ∨ isseq.fldtype then [Local.idx]
    else [Local.idx, symbol(builtinmod.fldtype, "pushflds", [fldtype], fldtype)])
   ),
 let constructor = symbol(modname, [name], if isseq then [typeint] + typs << 2 else typs << 1, recordtype),
 flds
  + symdef(
  constructor
  , constructflds + symbol(builtinmod.recordtype, "buildrecord", [recordtype], typeptr)
  , 0
 )
  + if isseq then
  let seqtype = seqof.para.modname,
  [
   symdef(symbol(modname, "toseq", [recordtype], seqtype), [Local.1], 0)
   , symdef(
    symbol4(modname, "to" sub 1, recordtype, [seqtype], recordtype)
    , ifthenelse([Local.1, GetSeqType, Fref.indexfunc, EqOp], [Local.1], [Sequence(typeint, 0)], typeptr)
    , 0
   )
  ]
   + (if name = "seq" sub 1 then
   [
    symdef(symbol(builtinmod.recordtype, "length", [recordtype], typeint), [Local.1, GetSeqLength], 0)
    , symdef(
     symbol(builtinmod.recordtype, "getseqtype", [recordtype], typeint)
     , [Local.1, GetSeqType]
     , 0
    )
   ]
  else empty:seq.symdef)
 else empty:seq.symdef

function fldsym(
modname:modref
, name:word
, objecttype:mytype
, fldtype:mytype
, knownsize:int
, unknownsize:seq.symbol
) symdef
let fldsym = symbol(modname, [name], [objecttype], fldtype),
symdef(
 fldsym
 , [Local.1, Lit.knownsize]
  + unknownsize
  + Getfld(if isseq.fldtype then typeptr else fldtype)
 , 0
)

function knownsize(fldtype:mytype) int
if fldtype ∈ [typeint, typeword, typereal, typeboolean, typeseqdec]
∨ isseq.fldtype
∨ isencoding.fldtype then 1
else 0

function findindex(
t2:symbol
, s:seq.symdef
, newsym:symbol
, allsrc:seq.seq.word
) seq.symdef
let w = symdef(t2, empty:seq.symbol, 0),
if module.newsym = module.t2 then s
else
 for i = 1, e ∈ s while sym.e ≠ sym.w ∨ (allsrc sub paragraphno.e) sub 1 ∉ "Export" do i + 1,
 if i > n.s then s
 else
  subseq(s, 1, i - 1)
   + symdef(newsym, empty:seq.symbol, paragraphno.s sub i)
   + subseq(s, i + 1, n.s)

function resolve(all:set.passsymbols, p:passsymbols, allsrc:seq.seq.word) passsymbols
if isempty.unresolvedexports.p then p
else
 let r = formsymboldict(all, p, empty:set.symdef, "symbol" sub 1)
 let dict = symboldict(syms.r, req.r),
 for
  exports = exports.p
  , unresolved = empty:set.symbol
  , newtext = srclink.p
  , t2 ∈ toseq.unresolvedexports.p
 do
  let b = lookupbysig(dict, t2),
  if checkreturntype(b, t2) then next(exports + b sub 1, unresolved, findindex(t2, newtext, b sub 1, allsrc))
  else next(exports, unresolved + t2, newtext),
 passsymbols(modname.p, uses.p, defines.p, exports, unresolved, typedict.p, newtext)

function checkreturntype(b:set.symbol, t2:symbol) boolean
if n.b = 1 then
 let t = resulttype.b sub 1 = resulttype.t2
 assert t report "Export result type does not match:(t2)",
 t
else false

function resolveexports(
s1:set.passsymbols
, countin:int
, allsrc:seq.seq.word
) set.passsymbols
if countin = 0 then s1
else
 for cnt = 0, acc = empty:set.passsymbols, p ∈ toseq.s1
 do next(cnt + n.unresolvedexports.p, acc + resolve(s1, p, allsrc))
 assert countin ≠ cnt report
  for acc2 = "", p2 ∈ toseq.s1 do acc2 + printunresolved.p2,
  acc2,
 resolveexports(acc, cnt, allsrc)

function printunresolved(p:passsymbols) seq.word
let txt =
 for acc = "", t ∈ toseq.unresolvedexports.p
 do acc + %.t,
 acc,
if isempty.txt then ""
else "module:(modname.p) contains unresolved exports::(txt) /br"

Function formsymboldict(
modset:set.passsymbols
, this:passsymbols
, requireUnbound:set.symdef
, mode:word
) partdict
{bug here should not need i = 0 in forloop}
for syms = defines.this, requires = empty:set.symdef, i = 0, u ∈ toseq.uses.this
do
 let a = lookup(modset, passsymbols.abstractmod.u),
 if isempty.a then
  assert mode ∉ "body" report "Cannot find module" + name.u
  {needed for when modset passsymbols are not yet created}
  next(syms, requires, 0)
 else if not.isAbstract.modname.a sub 1 then next(syms ∪ exports.a sub 1, requires, 0)
 else
  let r =
   for acc = syms, req = requires, e ∈ toseq.exports.a sub 1
   do
    let sym2 = replaceTsymbol(para.u, e),
    if isempty.requireUnbound then next(acc + sym2, req)
    else
     let require = getSymdef(requireUnbound, e),
     if isempty.require then next(acc + sym2, req)
     else
      let list =
       for acc2 = empty:seq.symbol, sym4 ∈ code.require sub 1
       do acc2 + replaceTsymbol(para.u, sym4),
       acc2,
      next(acc + setrequires.sym2, req + symdef(sym2, list, 0)),
   partdict(acc, req),
  next(syms.r, req.r, 0),
partdict(syms, requires)

type partdict is syms:set.symbol, req:set.symdef

use seq1.mytype

Function findabstract(templates:set.symdef, sym:symbol) seq.findabstractresult
for acc = empty:seq.findabstractresult, sd ∈ toseq.templates
do
 let e = sym.sd,
 if name.e = name.sym ∧ n.types.e = n.types.sym ∧ para.module.e = typeT then
  for Tis0 = empty:set.mytype, idx = 1, t ∈ types.e
  do
   let S = solveT(t, (types.sym) sub idx),
   next(if S = type? then Tis0 else Tis0 + S, idx + 1)
  let S = solveT(<<.typeT, para.module.sym)
  let Tis1 = if S = type? then Tis0 else Tis0 + S,
  for Tis = empty:seq.mytype, t ∈ toseq.Tis1
  do if sym >2 replaceTsymbol(t, e) = EQ then Tis + t else Tis,
  if isempty.Tis then acc
  else if sym >1 e = EQ ∨ isunbound.e then acc
  else acc + findabstractresult(sd, Tis sub 1)
 else acc,
acc

type findabstractresult is sd:symdef, modpara:mytype

function solveT(a:mytype, b:mytype) mytype
if a = typeT then b
else if isAbstract.a ∧ abstracttypename.a = abstracttypename.b then solveT(parameter.a, parameter.b)
else if isAbstract.a ∧ abstracttypename.a ∈ ">> <<" ∧ not.isSimple.b then b
else type?

Function module(f:passsymbols) modref modname.f

type passsymbols is
modname:modref
, uses:set.modref
, defines:set.symbol
, exports:set.symbol
, unresolvedexports:set.symbol
, typedict:set.mytype
, srclink:seq.symdef

Function passsymbols(modname:modref) passsymbols
passsymbols(
 modname
 , empty:set.modref
 , empty:set.symbol
 , empty:set.symbol
 , empty:set.symbol
 , empty:set.mytype
 , empty:seq.symdef
)

Function passsymbols(modname:modref, uses:set.modref) passsymbols
passsymbols(
 modname
 , uses
 , empty:set.symbol
 , empty:set.symbol
 , empty:set.symbol
 , empty:set.mytype
 , empty:seq.symdef
)

Function >1(a:passsymbols, b:passsymbols) ordering module.a >1 module.b

function checkwellformed(sym:symbol) boolean
if isSimple.module.sym then
 for acc = false, t ∈ types.sym while not.acc do isAbstract.t,
 not.acc
else
 for acc = false, t ∈ types.sym >> 1 while not.acc do isAbstract.t,
 acc
 
