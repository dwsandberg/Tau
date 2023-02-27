Module symbolconstant

use standard

use symbol

use seq.symbol

use sparseseq.symbol

use symbol2

use encoding.symbolconstant

use seq.symdef

use set.symdef

Export type:symbolconstant

Function seqelements(s:symbol) seq.symbol
if iswords.s then
 for acc = empty:seq.symbol, w ∈ worddata.s do acc + Word.w /do acc
else
 assert isrecordconstant.s report "constant code error $(s)"
 let code1 = fullconstantcode.s
 assert isSequence.last.code1 report "constant code error 21 $(code1)",
 code1 >> 1

Function fullconstantcode(s:symbol) seq.symbol
let t = findencode.symdef(s, empty:seq.symbol, 0)
assert not.isempty.t
report
 "unregister symbolconstant $(s)
  $(for txt = "", sd ∈ toseq.constantsymbols.first."X" do
  txt + "/p" + %.sym.sd + %.code.sd
 /do txt)
  "
,
code.t_1

use encoding.symdef

Function Constant2(libname:word, args:seq.symbol) symbol
for hasfref = false, sym ∈ args
while not.hasfref
do
 hasfref.sym
/do
 let flags = if hasfref then constbit ∨ hasfrefbit else constbit
 let i = addorder.symbolconstant(args, flags)
 let sym2 = 
  symbol(moduleref."internallib $constant"
   , [merge.[libname, "."_1, toword.i]]
   , empty:seq.mytype
   , typeptr
   , flags)
 let discard = encode.symdef(sym2, args, 0),
 sym2

Function registerConstant(sd:symdef) symdef
let discard = encode.sd,
sd

use set.symbol

function =(a:symdef, b:symdef) boolean sym.a = sym.b

function hash(a:symdef) int hash.sym.a

Function hash(s:seq.symbol) int
hash.for acc = "", e ∈ s do acc + worddata.e + name.module.e /do acc

type symbolconstant is toseq:seq.symbol, flags:bits

function =(a:symbolconstant, b:symbolconstant) boolean toseq.a = toseq.b

function hash(a:symbolconstant) int hash.toseq.a

use seq.mytype

use bits

Function constantsymbols(libname:word) set.symdef asset.encodingdata:symdef 