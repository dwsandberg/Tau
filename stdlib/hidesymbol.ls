Module hidesymbol

use standard

use mytype

use seq.symbol

use otherseq.mytype

use bits

use otherseq.word

type symbol is worddata:seq.word, module:modref,types:seq.mytype, raw:bits,hashbits:bits, zcode:seq.symbol

Export type:symbol

Export worddata(symbol) seq.word

Export module(symbol)modref

Export types(symbol)seq.mytype

Export raw(symbol)bits

Export zcode(symbol) seq.symbol

Function =(a:symbol, b:symbol)boolean
 hashbits.a = hashbits.b ∧ worddata.a = worddata.b ∧ (types.a >> 1= types.b >> 1) 
 ∧ issimplename.a = issimplename.b
 ∧ module.a = module.b

 /and (name.module.a /nin "$fref"  /or zcode.a=zcode.b)

Function ?(a:symbol, b:symbol)ordering
 fsighash.a ? fsighash.b ∧ worddata.a ? worddata.b ∧ (types.a >> 1)  ? (types.b  >> 1) 
  ∧ issimplename.a ? issimplename.b
 ∧ module.a ? module.b
 
Function ?2(a:symbol, b:symbol)ordering 
 fsighash.a ? fsighash.b ∧ worddata.a ? worddata.b ∧ (types.a >> 1) ? (types.b  >> 1)
 ∧ issimplename.a ? issimplename.b

function extrabits(types:seq.mytype,other:int,flags:bits) bits
 bits.hash( types ,other) << 4 ∨ (flags /and 0x0F)
 
Function extrabits(s:symbol)int toint.hashbits.s

Function Words(s:seq.word)symbol 
symbol(s, moduleref."$words",[ typeptr],0x0,extrabits(empty:seq.mytype,hash.s,constbit), empty:seq.symbol)

Function specialbit bits bits.4

Function simplenamebit bits bits.2

Function constbit bits bits.1

Function issimplename(sym:symbol) boolean (hashbits.sym /and simplenamebit) /ne 0x0 

Function isspecial(s:symbol)boolean(hashbits.s ∧ specialbit) = specialbit

Function isconst(s:symbol)boolean(hashbits.s ∧ constbit) = constbit

Function isunbound(sym:symbol)boolean (raw.sym /and unboundbit) /ne 0x0

function unboundbit bits  0x1 << 41

function requiresbit bits  0x1 << 42

Function hasrequires(sym:symbol)boolean (raw.sym /and requiresbit) /ne 0x0

Function hash(sym:symbol)int toint(hashbits.sym >> 4)

Function fsighash(s:symbol)int toint(hashbits.s >> 4)

Function setunbound(sym:symbol) symbol
  symbol( worddata.sym,module.sym,types.sym,raw.sym /or unboundbit,hashbits.sym,empty:seq.symbol) 

Function setrequires(sym:symbol)symbol 
 symbol( worddata.sym,module.sym,types.sym,raw.sym /or requiresbit,hashbits.sym,empty:seq.symbol) 

Function addzcode (s:symbol,zcode:seq.symbol) symbol
 symbol(worddata.s, module.s,types.s, raw.s,hashbits.s,  zcode)

Function replaceTsymbol(with:mytype, sym:symbol)symbol
 if with = typeT /or isconst.sym then sym else
let newtypes = for newtypes = empty:seq.mytype, t = types.sym do newtypes + replaceT(with, t)/for(newtypes)
symbol( worddata.sym,replaceT(with, module.sym), newtypes, raw.sym,extrabits(newtypes,   hash.worddata.sym,hashbits.sym),empty:seq.symbol)

Function symbolZ(module:modref, name:word,namePara:seq.mytype,paras:seq.mytype,rt:mytype,flags:bits,raw:bits) symbol
   let types=namePara+paras+rt
  symbol([name] ,   module , types,raw
  , extrabits( types ,hash.[name],
  if isempty.namePara  then simplenamebit /or flags else flags),  empty:seq.symbol )
  
Function Br2(t:int, f:int)symbol
 let raw=bits.t << 20 ∨ bits.f
 symbolZ(moduleref("$br"),"BR2"_1, 
  [ typeref([ toword.toint.raw,"."_1,"."_1])  ]
  ,empty:seq.mytype,type?,specialbit,bits.t << 20 ∨ bits.f)

Function brt(s:symbol)int toint(raw.s >> 20 ∧ 0xFFFFF)

Function brf(s:symbol)int toint(raw.s ∧ 0xFFFFF)

Function type? mytype  typeref( "? internal .") 

Function printrep(s :symbol) seq.word
    if name.module.s = "$int"_1 then [ name.s]
    else   if iswords.s then   '"'+ worddata.s+'"' 
    else 
     "("+[library.module.s,name.module.s]+ printrep.para.module.s
    +name.s+toword.toint.raw.s 
    +for acc = "", t =  types.s   do
     acc + printrep.t  
    /for(acc   + ")")/if

Function name(sym:symbol) word first.worddata.sym 


Function iswords(s:symbol)boolean name.module.s ∈ "$words"

Function islocal(s:symbol)boolean name.module.s ∈ "$local " 

Function isdefine(s:symbol)boolean name.module.s ∈ "$define"

Function isbr(s:symbol)boolean name.module.s ∈ "$br"

Function isexit(s:symbol)boolean name.module.s ∈ "$exitblock"

Function isparameter(s:symbol)boolean    name.module.s ∈ "$parameter" 

Function value(sym:symbol)int toint.raw.sym

Function nopara(s:symbol)int
 if isconst.s ∨ islocal.s ∨ isparameter.s then 0
 else if isspecial.s ∧ name.module.s ∉ "$record $loopblock"then
  if   isdefine.s ∨ isbr.s /or isexit.s then 1
  else
  { assert name.module.s  /in "$continue $sequence " report "CHeKC"+print.s}
    toint.name.s
 else 
  length.types.s-if issimplename.s then  1 else  2



___________________________________________________________

module hashset.T

use bits

use standard

use seq.T

use otherseq.seq.T

use seq.seq.T

type hashset is table:seq.seq.T, cardinality:int, mask:bits

unbound hash(T)int

unbound =(T, T)boolean

Function ∪(a:hashset.T, b:hashset.T)hashset.T
 if cardinality.b > cardinality.a then b ∪ a
 else for acc = a, e = toseq.b do acc + e /for(acc)

function clean(s:seq.T, mask:bits, idx:int)seq.T
let currenthash = tobits(idx - 1)
 for acc = empty:seq.T, e = s do
  if e ∈ acc ∨ (tobits.hash.e ∧ mask) ≠ currenthash then acc else acc + e
 /for(acc)

Function +(s:hashset.T, a:T)hashset.T
let idx = toint(tobits.hash.a ∧ mask.s) + 1
 assert between(idx, 1, length.table.s)report"XXX" + print.idx + print.length.table.s + print.mask.s
 let list =(table.s)_idx
 let t = replace(table.s, idx, clean([ a] + list, mask.s, idx))
  assert not.isempty.clean([ a] + list, mask.s, idx)report"XX"
   if a ∈ list then hashset(t, cardinality.s, mask.s)
   else
    let newmask = bits.-1 >> (64 - floorlog2((cardinality.s + 1) * 3 / 2))
     if toint.newmask ≤ toint.mask.s then hashset(t, cardinality.s + 1, mask.s)
     else hashset(t + t, cardinality.s + 1, mask.s << 1 ∨ 0x1)

Function findelement(ele:T, s:hashset.T)seq.T
let idx = toint(tobits.hash.ele ∧ mask.s) + 1
 findelement(ele,(table.s)_idx)

Function toseq(s:hashset.T)seq.T
 for acc = empty:seq.T, idx = 1, e = table.s do
  next(acc + clean(e, mask.s, idx), idx + 1)
 /for(acc)

Function empty:hashset.T hashset.T hashset([ empty:seq.T, empty:seq.T, empty:seq.T, empty:seq.T], 0, 0x3)

Export type:hashset.T

Export cardinality(hashset.T)int


