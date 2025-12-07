Module symbolconstant

use bits

use mytype

use seq.mytype

use standard

use seq1.symbol

use symbol

use encoding.symbolconstant

use encoding.symdef

use seq.symdef

use set.symdef

Export symdefOption(i:int) symdefOption

Export type:symbolconstant

Export type:symdef

Export code(symdef) seq.symbol

Export sym(sd:symdef) symbol

Export type:symdefOption

Export toint(symdefOption) int

Function fullconstantcode(s:symbol) seq.symbol
let t = findencode.symdef(s, empty:seq.symbol, 0)
assert not.isempty.t report
 "unregister symbolconstant:(s):(for txt = "", sd ∈ toseq.constantsymbols."X" sub 1 do txt + "/p" + %.sym.sd + %.code.sd,
 txt):(stacktrace)",
code.t sub 1

Function Constant2(libname:word, args:seq.symbol) symbol
let i = addorder.symbolconstant.args
let sym2 = symbolC(i, libname)
let discard = encode.symdef(sym2, args, 0),
sym2

Function registerConstant(sd:symdef) symdef
let discard = encode.sd,
sd

Function =(a:symdef, b:symdef) boolean sym.a = sym.b

function hash(a:symdef) int hash.sym.a

Function hash(s:seq.symbol) int
for acc = "", e ∈ s do acc + worddata.e + name.module.e,
hash.acc

type symbolconstant is toseq:seq.symbol

function =(a:symbolconstant, b:symbolconstant) boolean toseq.a = toseq.b

function hash(a:symbolconstant) int hash.toseq.a

Function constantsymbols(libname:word) set.symdef asset.encodingdata:symdef

---------------

type symdef is sym:symbol, code:seq.symbol, bits:bits

Function symdef(sym:symbol, code:seq.symbol, pno:int) symdef
symdef(sym, code, bits.pno)

Function paragraphno(sd:symdef) int toint(0xFFFFFFFFFFFF ∧ bits.sd)

Function externalNo(sd:symdef) int toint(0xFFFFFFFFFFFF ∧ bits.sd)

Function >1(a:symdef, b:symdef) ordering sym.a >1 sym.b

Function getSymdef(a:set.symdef, sym:symbol) set.symdef
lookup(a, symdef(sym, empty:seq.symbol, 0))

Function isThisLibrary(sd:symdef) boolean
let XThisLibrary = 0x1000000000000,
(bits.sd ∧ XThisLibrary) ≠ 0x0

Function symdef4(
sym:symbol
, code:seq.symbol
, paragraphno:int
, options:symdefOption
) symdef
symdef(sym, code, bits.paragraphno ∨ tobits.toint.options << 48)

Function ∈(a:symdefOption, b:symdefOption) boolean
(tobits.toint.a ∧ tobits.toint.b) = tobits.toint.a

Function %(a:symdefOption) seq.word
for i = 1, acc = tobits.toint.a, result = ""
while acc ≠ 0x0
do
 let new =
  if (acc ∧ 0x1) = 0x1 then
   result
   + "ThisLibrary PROFILE STATE COMPILETIME NOINLINE INLINE VERYSIMPLE COMMAND nonReducible" sub i
  else result,
 next(i + 1, acc >> 1, new),
result

Function options(sd:symdef) symdefOption symdefOption.toint(bits.sd >> 48)

Function getCode(a:set.symdef, sym:symbol) seq.symbol
let b = getSymdef(a, sym),
if isempty.b then empty:seq.symbol else code.b sub 1

Function +(a:symdefOption, b:symdefOption) symdefOption
symdefOption.toint(tobits.toint.a ∨ tobits.toint.b)

Function ∩(a:symdefOption, b:symdefOption) symdefOption
symdefOption.toint(tobits.toint.a ∧ tobits.toint.b)

Function \(a:symdefOption, b:symdefOption) symdefOption
symdefOption.toint(tobits.toint.a ∧ (0xFFFF ⊻ tobits.toint.b))

function genEnum seq.seq.word
["newType: symdefOption nameValue: NOOPTIONS 0 ThisLibrary 0x1 PROFILE 0x2 STATE 0x4 COMPILETIME 0x8 NOINLINE 0x10 INLINE 0x20 VERYSIMPLE 0x40 COMMAND 0x80 nonReducible 0x100"]

<<<< Below is auto generated code >>>>

type symdefOption is toint:int

Export toint(symdefOption) int

Export symdefOption(i:int) symdefOption

Export type:symdefOption

Function =(a:symdefOption, b:symdefOption) boolean toint.a = toint.b

Function NOOPTIONS symdefOption symdefOption.0

Function ThisLibrary symdefOption symdefOption.1

Function PROFILE symdefOption symdefOption.2

Function STATE symdefOption symdefOption.4

Function COMPILETIME symdefOption symdefOption.8

Function NOINLINE symdefOption symdefOption.16

Function INLINE symdefOption symdefOption.32

Function VERYSIMPLE symdefOption symdefOption.64

Function COMMAND symdefOption symdefOption.128

Function nonReducible symdefOption symdefOption.256

Function decode(code:symdefOption) seq.word
let discard =
 [
  NOOPTIONS
  , ThisLibrary
  , PROFILE
  , STATE
  , COMPILETIME
  , NOINLINE
  , INLINE
  , VERYSIMPLE
  , COMMAND
  , nonReducible
 ]
let i = toint.code,
if i = 0 then "NOOPTIONS"
else if i = 1 then "ThisLibrary"
else if i = 2 then "PROFILE"
else if i = 4 then "STATE"
else if i = 8 then "COMPILETIME"
else if i = 16 then "NOINLINE"
else if i = 32 then "INLINE"
else if i = 64 then "VERYSIMPLE"
else if i = 128 then "COMMAND"
else if i = 256 then "nonReducible"
else "symdefOption." + toword.i 