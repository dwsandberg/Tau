Module passsymbol

use mytype

use parse

use standard

use symbol

use symboldict

use seq.commoninfo

use seq.findabstractresult

use set.modref

use seq.mytype

use set.mytype

use seq.passsymbols

use set.passsymbols

use seq.passtypes

use set.passtypes

use encoding.symbol

use graph.symbol

use seq.symbol

use set.symbol

use seq.symdef

use set.symdef

use seq.symtextpair

use set.word

use seq.seq.mytype

use seq.arc.symbol

use set.arc.symbol

use seq.seq.symbol

use seq.seq.symdef

use seq.set.symdef

use set.arc.seq.word

Function resolvesymbols(t:seq.seq.word, lib:word, mods:set.passtypes, libmods:set.passsymbols)prg6
let passtypes = mods
for typeflds = empty:seq.seq.mytype
, paragraphno = 1
, text = empty:seq.symtextpair
, modlist = libmods
, defines = empty:seq.symbol
, exports = empty:set.symbol
, unresolvedexports = empty:set.symbol
, uses = empty:set.modref
, common = commoninfo("", internalmod, lib, empty:set.mytype, "symbol"_1)
, typearcs = empty:seq.symdef
, m ∈ t
do
 let input = m
 if isempty.input then
  next(typeflds, paragraphno + 1, text, modlist, defines
  , exports, unresolvedexports, uses, common, typearcs
  )
 else if first.input ∈ "Module module"then
  let x = findpasstypes(passtypes, lib, input)
  let z = commoninfo(input, modname.x_1, lib, formtypedict(passtypes, x_1), "symbol"_1)
  assert not.isempty.x report"did not find" + input
  let lastpass = 
   resolve(empty:set.passsymbols
   , passsymbols(modname.common, uses, asset.defines, exports, unresolvedexports, types.common, text)
   )
  next(typeflds
  , paragraphno + 1
  , empty:seq.symtextpair
  , modlist + lastpass
  , empty:seq.symbol
  , empty:set.symbol
  , empty:set.symbol
  , uses.x_1
  , z
  , typearcs
  )
 else if first.input ∈ "Function function Builtin builtin Export unbound"then
  let b = 
   parse.symboldict(empty:set.symbol
   , [commoninfo(getheader.input, modname.common, lib.common, types.common, "symbol"_1)]
   )
  let modname = 
   if first.input ∈ "Builtin builtin"then
    if issimple.modname.common then internalmod else modname.common
   else modname.common
  let sym = 
   if length.text.b = 1 then
    let name = text.b
    if name = "true"then Littrue
    else if name = "false"then Litfalse else symbol(modname, text.b, types.b >> 1, last.types.b)
   else
    symbol4(modname, first.text.b, first.types.b, subseq(types.b, 2, length.types.b - 1), last.types.b)
  assert checkwellformed.sym
  report"Must use type T in function name or parameters in parameterized module and T cannot be used in non-parameterized module 
"
  + getheader.input
  if first.input = "unbound"_1 then
   next(typeflds
   , paragraphno + 1
   , text
   , modlist
   , defines + setunbound.sym
   , exports
   , unresolvedexports
   , uses
   , common
   , typearcs
   )
  else if first.input = "Export"_1 then
   next(typeflds
   , paragraphno + 1
   , text
   , modlist
   , defines
   , exports
   , unresolvedexports + sym
   , uses
   , common
   , typearcs
   )
  else
   assert sym ∉ defines
   report"Function" + wordname.sym + "is defined twice in module" + print.modname
   next(typeflds
   , paragraphno + 1
   , text + symtextpair(sym, m, paragraphno)
   , modlist
   , defines + sym
   , if first.input ∈ "Function Builtin"then exports + sym else exports
   , unresolvedexports
   , uses
   , common
   , typearcs
   )
 else if first.input ∈ "type"then
  let b = 
   parse.symboldict(empty:set.symbol
   , [commoninfo(input, modname.common, lib.common, types.common + typeseqdec, "symbol"_1)]
   )
  let typs = types.b
  let typesym = {deepcopy is used to represent type}deepcopySym.first.typs
  let isseq = typs_2 = typeseqdec
  let flds = flds(isseq, text.b, modname.common, input_2, typs)
  let newdefines = for acc = defines + typesym, sd ∈ flds do acc + sym.sd /for(acc)
  let tt = if isseq then[first.typs, typeint, typeint] + typs << 2 else typs
  next(typeflds + tt, paragraphno + 1, text, modlist, newdefines
  , exports, unresolvedexports, uses, common, typearcs + flds
  )
 else
  next(typeflds, paragraphno + 1, text, modlist, defines
  , exports, unresolvedexports, uses, common, typearcs
  )
/for(let lastpass = 
 resolve(empty:set.passsymbols
 , passsymbols(modname.common, uses, asset.defines, exports, unresolvedexports, types.common, text)
 )
prg6(asset.typearcs, resolveexports(modlist + lastpass, 100000), typeflds))

Export type:symdef

Export type:prg6

Export code(prg6)set.symdef

Export modules(prg6)set.passsymbols

Export symdef(symbol, seq.symbol)symdef

Export sym(symdef)symbol

Export code(symdef)seq.symbol

type prg6 is code:set.symdef, modules:set.passsymbols, types:seq.seq.mytype

Export types(prg6)seq.seq.mytype

Function flds(isseq:boolean, binfotext:seq.word, modname:modref, name:word, typs:seq.mytype)seq.symdef
let recordtype = if issimple.modname then first.typs else addabstract(first.typs, typeT)
if not.isseq ∧ length.typs = 2 then
 let typ = recordtype
 if iscore4.typ then empty:seq.symdef
 else
  let fldtype = last.typs
  [symdef(symbol(modname, [name], fldtype, typ), [Local.1])
  , symdef(symbol(modname, binfotext, typ, fldtype), [Local.1])
  ]
  + setSymdef(recordtype, [fldtype])
else
 let indexfunc = symbol(modname, "_", recordtype, typeint, typeT)
 for flds = empty:seq.symdef
 , idx = 1
 , knownsize = if isseq then 1 else 0
 , unknownsize = empty:seq.symbol
 , constructflds = if isseq then[PreFref, indexfunc, Local.1]else empty:seq.symbol
 , fldtype ∈ if isseq then[typeint] + typs << 2 else typs << 1
 do
  let size = knownsize.fldtype
  let usize = 
   if size = 1 then unknownsize
   else unknownsize + symbol(builtinmod.fldtype, "typesize", typeint) + PlusOp
  if binfotext_idx ∈ ":"then next(flds, idx + 1, knownsize + size, usize, constructflds)
  else
   next(flds + fldsym(modname, binfotext_idx, recordtype, fldtype, knownsize, unknownsize)
   , idx + 1
   , knownsize + size
   , usize
   , constructflds
   + if fldtype = typeint ∨ isseq.fldtype then[Local.idx]
   else[Local.idx, symbol(builtinmod.fldtype, "pushflds", fldtype, fldtype)]
   )
 /for(let constructor = 
  symbol(modname
  , [name]
  , if isseq then[typeint] + typs << 2 else typs << 1
  , recordtype
  )
 flds
 + symdef(constructor
 , constructflds + symbol(builtinmod.recordtype, "buildrecord", recordtype, typeptr)
 )
 + if isseq then
  let seqtype = seqof.para.modname
  setSymdef(recordtype, [typeint, typeint] + typs << 2)
  + [symdef(symbol(modname, "toseq", recordtype, seqtype), [Local.1])
  , symdef(symbol4(modname, "to"_1, recordtype, [seqtype], recordtype)
  , ifthenelse([Local.1, GetSeqType, PreFref, indexfunc, EqOp]
  , [Local.1]
  , [Sequence(typeint, 0)]
  , typeptr
  )
  )
  ]
  + if name = "seq"_1 then
   [symdef(symbol(builtinmod.typeint, "length", recordtype, typeint), [Local.1, GetSeqLength])
   , symdef(symbol(builtinmod.typeint, "getseqtype", recordtype, typeint)
   , [Local.1, GetSeqType]
   )
   ]
  else empty:seq.symdef
 else setSymdef(recordtype, typs << 1)/if)

function fldsym(modname:modref
, name:word
, objecttype:mytype
, fldtype:mytype
, knownsize:int
, unknownsize:seq.symbol
)symdef
let fldsym = symbol(modname, [name], objecttype, fldtype)
symdef(fldsym
, [Local.1, Lit.knownsize] + unknownsize
+ Getfld.if isseq.fldtype then typeptr else fldtype
)

function knownsize(fldtype:mytype)int
if fldtype ∈ [typeint, typeword, typereal, typeboolean, typeseqdec] ∨ isseq.fldtype ∨ isencoding.fldtype then
 1
else 0

function setSymdef(recordtype:mytype, t:seq.mytype)seq.symdef
if false then
 [symdef(setSym.recordtype
 , for acc = [Local.1], idx = 0, fldtype ∈ t do next(acc + [Local.2, Lit.idx, Getfld.fldtype, setSym.fldtype], idx + 1)/for(acc)
 )
 ]
else empty:seq.symdef

type resultz is acc:seq.symdef, alluses:seq.symbol

function resolve(all:set.passsymbols, p:passsymbols)passsymbols
if isempty.unresolvedexports.p then p
else
 let z = commoninfo("", internalmod, "?"_1, empty:set.mytype, "symbol"_1)
 let r = formsymboldict(all, p, empty:set.symdef, "symbol"_1)
 let dict = symboldict(syms.r, req.r, [z])
 for exports = exports.p, unresolved = empty:set.symbol, t2 ∈ toseq.unresolvedexports.p do
  let b = lookupbysig(dict, t2)
  if checkreturntype(b, t2)then
   {assert resulttype.b_1=resulttype.t2 report"Return type of export does not match"+print.b_1}
   next(exports + b_1, unresolved)
  else next(exports, unresolved + t2)
 /for(passsymbols(modname.p, uses.p, defines.p, exports, unresolved, typedict.p, text.p))

function checkreturntype(b:set.symbol, t2:symbol)boolean
if cardinality.b = 1 then
 let t = resulttype.b_1 = resulttype.t2
 assert t report"Export result type does not match" + print.t2
 t
else false

assert resulttype.b_1=resulttype.t2 report"Return type of export does not match"+print.b_1 true

function resolveexports(s1:set.passsymbols, countin:int)set.passsymbols
if countin = 0 then s1
else
 {assert countin /in[100000, 101, 25]report"C"+print.countin}
 for cnt = 0, acc = empty:set.passsymbols, p ∈ toseq.s1 do next(cnt + cardinality.unresolvedexports.p, acc + resolve(s1, p))/for(assert countin ≠ cnt
 report for acc2 = "", p2 ∈ toseq.s1 do acc2 + printunresolved.p2 /for(acc2)
 resolveexports(acc, cnt))

function printunresolved(p:passsymbols)seq.word
let txt = 
 for acc = "", t ∈ toseq.unresolvedexports.p do acc + print.t /for(acc)
if isempty.txt then""
else"module" + print.modname.p + "contains unresolved exports:" + txt + EOL

Function print(s:seq.mytype)seq.word for acc = "", t ∈ s do acc + print.t /for(acc)

Export text(symtextpair)seq.word

Export type:symtextpair

Export paragraphno(symtextpair)int

Export sym(symtextpair)symbol

Export print(passsymbols)seq.word

Export type:passsymbols

Export text(passsymbols)seq.symtextpair

Export modname(passsymbols)modref

Export typedict(passsymbols)set.mytype

Export exports(passsymbols)set.symbol

function print(s:passsymbols)seq.word
EOL + "Module" + print.modname.s + EOL + "Defines" + EOL
+ for acc = "", t ∈ toseq.defines.s do acc + print.t + EOL /for(acc)
+ if isempty.unresolvedexports.s then""
else
 EOL + "Unresolved Export" + EOL
 + for acc = "", t ∈ toseq.unresolvedexports.s do acc + print.t + EOL /for(acc)

Function parse(input:seq.word, p:partdict, c:commoninfo)bindinfo
parse.symboldict(syms.p, req.p, [commoninfo(input, modname.c, lib.c, types.c, mode.c)])

Function formsymboldict(modset:set.passsymbols, this:passsymbols, requireUnbound:set.symdef, mode:word)partdict
{bug here should not need i=0 in forloop}
let dict = 
 for syms = defines.this, requires = empty:set.symdef, i = 0, u ∈ toseq.uses.this do
  let a = lookup(modset, passsymbols.abstractmod.u)
  if isempty.a then
   assert mode ∉ "body"report"Cannot find module" + name.u
   {needed for when modset passsymbols are not yet created}next(syms, requires, 0)
  else if not.isabstract.modname.a_1 then next(syms ∪ exports.a_1, requires, 0)
  else
   let r = 
    for acc = syms, req = requires, e ∈ toseq.exports.a_1 do
     let sym2 = replaceTsymbol(para.u, e)
     if isempty.requireUnbound then next(acc + sym2, req)
     else
      let require = lookup(requireUnbound, symdef(e, empty:seq.symbol))
      if isempty.require then next(acc + sym2, req)
      else
       let list = 
        for acc2 = empty:seq.symbol, sym4 ∈ code.require_1 do acc2 + replaceTsymbol(para.u, sym4)/for(acc2)
       {assert name.e /nin"arithseq"report"GHJ"+print.list}
       next(acc + setrequires.sym2, req + symdef(sym2, list))
    /for(partdict(acc, req))
   next(syms.r, req.r, 0)
 /for(partdict(syms, requires))
partdict(for acc = empty:set.symbol, sd ∈ toseq.req.dict do acc + setrequires.sym.sd /for(for acc2 = acc, sym ∈ toseq.syms.dict do acc2 + sym /for(acc2))
, req.dict
)


type partdict is syms:set.symbol, req:set.symdef

Function findabstract(templates:set.symdef, sym:symbol)seq.findabstractresult
for acc = empty:seq.findabstractresult, sd ∈ toseq.templates do
 let e = sym.sd
 if name.e = name.sym ∧ length.types.e = length.types.sym ∧ para.module.e = typeT then
  let z = 
   for Tis = type?, idx = 1, t ∈ types.e do
    let S = solveT(t, (types.sym)_idx)
    if S = type? then
     {assert t=(types.s)_idx report"XXXXX"+print.t+print.(types.s)_idx}next(Tis, idx + 1)
    else next(S, idx + 1)
   /for(Tis)
  if ?2(sym, replaceTsymbol(z, e)) = EQ then
   if(sym ? e) = EQ ∨ isunbound.e then acc else acc + findabstractresult(sd, z)
  else acc
 else acc
/for(acc)

type findabstractresult is sd:symdef, modpara:mytype

Function sym(a:findabstractresult)symbol sym.sd.a

Export type:findabstractresult

Export sd(findabstractresult)symdef

Export modpara(findabstractresult)mytype

function solveT(a:mytype, b:mytype)mytype
if a = typeT then b
else if isabstract.a ∧ abstracttypename.a = abstracttypename.b then solveT(parameter.a, parameter.b)
else type?

------------

type symtextpair is sym:symbol, text:seq.word, paragraphno:int

Export symtextpair(sym:symbol, text:seq.word, paragraphno:int)symtextpair

Export text(symtextpair)seq.word

Export type:symtextpair

Export paragraphno(symtextpair)int

Export sym(symtextpair)symbol

Export type:passsymbols

Function module(f:passsymbols)modref modname.f

Export modname(f:passsymbols)modref

Export typedict(passsymbols)set.mytype

Export defines(passsymbols)set.symbol

Export exports(passsymbols)set.symbol

Export uses(passsymbols)set.modref

Export text(passsymbols)seq.symtextpair

type passsymbols is modname:modref
, uses:set.modref
, defines:set.symbol
, exports:set.symbol
, unresolvedexports:set.symbol
, typedict:set.mytype
, text:seq.symtextpair


Export passsymbols(modname:modref, uses:set.modref, defines:set.symbol, exports:set.symbol, unresolvedexports:set.symbol, typedict:set.mytype, text:seq.symtextpair)passsymbols

Function passsymbols(modname:modref, uses:set.modref)passsymbols
passsymbols(modname
, uses
, empty:set.symbol
, empty:set.symbol
, empty:set.symbol
, empty:set.mytype
, empty:seq.symtextpair
)

Function passsymbols(modname:modref)passsymbols
passsymbols(modname
, empty:set.modref
, empty:set.symbol
, empty:set.symbol
, empty:set.symbol
, empty:set.mytype
, empty:seq.symtextpair
)

Function ?(a:passsymbols, b:passsymbols)ordering module.a ? module.b

function checkwellformed(sym:symbol)boolean
not.issimple.module.sym
= for acc = false, t ∈ types.sym while not.acc do isabstract.t /for(acc) 