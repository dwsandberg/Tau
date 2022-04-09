Module symbolconstant

use standard

use symbol

use seq.mytype

use seq.symbol

use encoding.symbolconstant

use set.symdef

Function constantcode(s:symbol)seq.symbol
let code1 = fullconstantcode.s
if isSequence.last.code1 then[Lit.0, Lit.nopara.last.code1] + code1 >> 1 else code1 >> 1

Function fullconstantcode(s:symbol)seq.symbol
assert isrecordconstant.s report"constant code error" + print.s  
toseq.decode.to:encoding.symbolconstant(toint.name.s)

Function Constant2(p:set.symdef, args:seq.symbol)symbol
let testsym = symconst.nextencoding.symbolconstant.empty:seq.symbol
let a = lookup(p, symdef(testsym, args))
if not.isempty.a then
 let discard = encode.symbolconstant.code.a_1
 Constant2(p, args)
else symconst.valueofencoding.encode.symbolconstant.args

Function Constant2(args:seq.symbol)symbol symconst.valueofencoding.encode.symbolconstant.args

Function hash(s:seq.symbol)int
hash.for acc = "", e ∈ s do acc + worddata.e + name.module.e /for(acc)

function assignencoding(a:symbolconstant)int nextencoding.a

Export type:symbolconstant

type symbolconstant is toseq:seq.symbol

function =(a:symbolconstant, b:symbolconstant)boolean toseq.a = toseq.b

function hash(a:symbolconstant)int hash.toseq.a

Function removeconstantcode(s:seq.symbol)seq.symbol
for acc = empty:seq.symbol, @e ∈ s do
 acc
 + if isrecordconstant.@e then removeconstantcode.fullconstantcode.@e else[@e]
/for(acc)

Function constantsymbols set.symdef
for acc = empty:set.symdef, p ∈ encoding:seq.encodingpair.symbolconstant do acc + symdef(symconst.valueofencoding.code.p, toseq.data.p)/for(acc) 