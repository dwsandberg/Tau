module llvmconstants

use standard

function generatecode seq.word
{generates code in this module beyond---------}
{cmp2op found llvm/IR/InstrTypes.h}
enumerate("align", "unspecified ? ? ? align8 align16 align32 align64")
+ enumerate("instop"
, "? BLOCKBINOP CAST ? SELECT ? ? ? ? RET BR ? ? ? ? PHI ? ? ALLOCA LOAD ? ? ? ? ? ? ? CMP2 ? ? ? ? ? CALL ? ? ? ? ? ? ? ? GEP STORE"
)
+ enumerate("typeop"
, "? NumEle TVOID ? DOUBLE ? OPAQUE INTEGER POINTER ? ? ARRAY ? ? ? ? ? ? ? ? ? FUNCTION"
)
+ enumerate("blockop"
, "INFOBLOCK? ? ? ? ? ? ? MODULE PARA PARAGRP CONSTANTS FUNCTIONBLK? VALUESYMTABLE ? ? TYPES"
)
+ enumerate("moduleop", "? Version TRIPLE LAYOUT ? ? ? GLOBALVAR FUNCTIONDEC")
+ enumerate("constop"
, "? SETTYPE CNULL CUNDEF CINTEGER CWIDEINTEGER CFLOAT CAGGREGATE CSTRING2 CSTRING0 CBINOP CCAST ? ? ? ? ? ? ? ? CGEP ? CDATA 
"
)
+ enumerate("castop"
, "trunc zext sext fptoui fptosi uitofp sitofp fptrunc fpext ptrtoint inttoptr bitcast"
)
+ enumerate("binaryop", "add sub mul udiv sdiv urem srem shl lshr ashr and or xor")
+ enumerate("cmp2op"
, "? Feq Fgt Fge Flt Fle Fne ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? eq ne ugt uge ult ule sgt sge slt sle"
)

function enumerate(type:seq.word, codes:seq.word)seq.word
"type" + type + "is toint:int" + " /br  /br Function decode(code:" + type
+ ")seq.word  /br let i=toint.code  /br if between(i+1, 1, "
+ toword.length.codes
+ ")then  /br let r=["
+ dq.codes
+ "_(i+1)]if not(r="
+ dq."?"
+ ")then r else"
+ dq(type + ".")
+ "+toword.i  /br else"
+ dq(type + ".")
+ "+toword.i  /br  /br Export toint("
+ type
+ ")int  /br  /br Export"
+ type
+ "(i:int)"
+ type
+ " /br  /br Export type:"
+ type
+ " /br  /br Function=(a:"
+ type
+ ", b:"
+ type
+ ")boolean toint.a=toint.b"
+ for acc = "", @e ∈ arithseq(length.codes, 1, 1)do acc + dd(type, codes, @e)/for(acc)
+ " /br  /br"

function dd(type:seq.word, w:seq.word, i:int)seq.word
if w_i = "?"_1 then""
else" /br  /br Function" + w_i + type + type + "." + toword(i - 1)

--------------------------

type align is toint:int

Function decode(code:align)seq.word
let i = toint.code
if between(i + 1, 1, 8)then
 let r = ["unspecified ? ? ? align8 align16 align32 align64"_(i + 1)]
 if r ≠ "?"then r else"align" + toword.i
else"align" + toword.i

Export toint(align)int

Export align(i:int)align

Export type:align

Function =(a:align, b:align)boolean toint.a = toint.b

Function unspecified align align.0

Function align8 align align.4

Function align16 align align.5

Function align32 align align.6

Function align64 align align.7

type instop is toint:int

Function decode(code:instop)seq.word
let i = toint.code
if between(i + 1, 1, 45)then
 let r = 
  ["? BLOCKBINOP CAST ? SELECT ? ? ? ? RET BR ? ? ? ? PHI ? ? ALLOCA LOAD ? ? ? ? ? ? ? CMP2 ? ? ? ? ? CALL ? ? ? ? ? ? ? ? GEP STORE"
  _(i + 1)
  ]
 if r ≠ "?"then r else"instop" + toword.i
else"instop" + toword.i

Export toint(instop)int

Export instop(i:int)instop

Export type:instop

Function =(a:instop, b:instop)boolean toint.a = toint.b

Function BLOCK instop instop.1

Function BINOP instop instop.2

Function CAST instop instop.3

Function SELECT instop instop.5

Function RET instop instop.10

Function BR instop instop.11

Function PHI instop instop.16

Function ALLOCA instop instop.19

Function LOAD instop instop.20

Function CMP2 instop instop.28

Function CALL instop instop.34

Function GEP instop instop.43

Function STORE instop instop.44

type typeop is toint:int

Function decode(code:typeop)seq.word
let i = toint.code
if between(i + 1, 1, 22)then
 let r = ["? NumEle TVOID ? DOUBLE ? OPAQUE INTEGER POINTER ? ? ARRAY ? ? ? ? ? ? ? ? ? FUNCTION"_(i + 1)]
 if r ≠ "?"then r else"typeop" + toword.i
else"typeop" + toword.i

Export toint(typeop)int

Export typeop(i:int)typeop

Export type:typeop

Function =(a:typeop, b:typeop)boolean toint.a = toint.b

Function NumEle typeop typeop.1

Function TVOID typeop typeop.2

Function DOUBLE typeop typeop.4

Function OPAQUE typeop typeop.6

Function INTEGER typeop typeop.7

Function POINTER typeop typeop.8

Function ARRAY typeop typeop.11

Function FUNCTION typeop typeop.21

type blockop is toint:int

Function decode(code:blockop)seq.word
let i = toint.code
if between(i + 1, 1, 18)then
 let r = ["INFOBLOCK? ? ? ? ? ? ? MODULE PARA PARAGRP CONSTANTS FUNCTIONBLK? VALUESYMTABLE ? ? TYPES"_(i + 1)]
 if r ≠ "?"then r else"blockop" + toword.i
else"blockop" + toword.i

Export toint(blockop)int

Export blockop(i:int)blockop

Export type:blockop

Function =(a:blockop, b:blockop)boolean toint.a = toint.b

Function INFOBLOCK blockop blockop.0

Function MODULE blockop blockop.8

Function PARA blockop blockop.9

Function PARAGRP blockop blockop.10

Function CONSTANTS blockop blockop.11

Function FUNCTIONBLK blockop blockop.12

Function VALUESYMTABLE blockop blockop.14

Function TYPES blockop blockop.17

type moduleop is toint:int

Function decode(code:moduleop)seq.word
let i = toint.code
if between(i + 1, 1, 9)then
 let r = ["? Version TRIPLE LAYOUT ? ? ? GLOBALVAR FUNCTIONDEC"_(i + 1)]
 if r ≠ "?"then r else"moduleop" + toword.i
else"moduleop" + toword.i

Export toint(moduleop)int

Export moduleop(i:int)moduleop

Export type:moduleop

Function =(a:moduleop, b:moduleop)boolean toint.a = toint.b

Function Version moduleop moduleop.1

Function TRIPLE moduleop moduleop.2

Function LAYOUT moduleop moduleop.3

Function GLOBALVAR moduleop moduleop.7

Function FUNCTIONDEC moduleop moduleop.8

type constop is toint:int

Function decode(code:constop)seq.word
let i = toint.code
if between(i + 1, 1, 23)then
 let r = 
  ["? SETTYPE CNULL CUNDEF CINTEGER CWIDEINTEGER CFLOAT CAGGREGATE CSTRING2 CSTRING0 CBINOP CCAST ? ? ? ? ? ? ? ? CGEP ? CDATA 
"
  _(i + 1)
  ]
 if r ≠ "?"then r else"constop" + toword.i
else"constop" + toword.i

Export toint(constop)int

Export constop(i:int)constop

Export type:constop

Function =(a:constop, b:constop)boolean toint.a = toint.b

Function SETTYPE constop constop.1

Function CNULL constop constop.2

Function CUNDEF constop constop.3

Function CINTEGER constop constop.4

Function CWIDEINTEGER constop constop.5

Function CFLOAT constop constop.6

Function CAGGREGATE constop constop.7

Function CSTRING2 constop constop.8

Function CSTRING0 constop constop.9

Function CBINOP constop constop.10

Function CCAST constop constop.11

Function CGEP constop constop.20

Function CDATA constop constop.22

type castop is toint:int

Function decode(code:castop)seq.word
let i = toint.code
if between(i + 1, 1, 12)then
 let r = ["trunc zext sext fptoui fptosi uitofp sitofp fptrunc fpext ptrtoint inttoptr bitcast"_(i + 1)]
 if r ≠ "?"then r else"castop" + toword.i
else"castop" + toword.i

Export toint(castop)int

Export castop(i:int)castop

Export type:castop

Function =(a:castop, b:castop)boolean toint.a = toint.b

Function trunc castop castop.0

Function zext castop castop.1

Function sext castop castop.2

Function fptoui castop castop.3

Function fptosi castop castop.4

Function uitofp castop castop.5

Function sitofp castop castop.6

Function fptrunc castop castop.7

Function fpext castop castop.8

Function ptrtoint castop castop.9

Function inttoptr castop castop.10

Function bitcast castop castop.11

type binaryop is toint:int

Function decode(code:binaryop)seq.word
let i = toint.code
if between(i + 1, 1, 13)then
 let r = ["add sub mul udiv sdiv urem srem shl lshr ashr and or xor"_(i + 1)]
 if r ≠ "?"then r else"binaryop" + toword.i
else"binaryop" + toword.i

Export toint(binaryop)int

Export binaryop(i:int)binaryop

Export type:binaryop

Function =(a:binaryop, b:binaryop)boolean toint.a = toint.b

Function add binaryop binaryop.0

Function sub binaryop binaryop.1

Function mul binaryop binaryop.2

Function udiv binaryop binaryop.3

Function sdiv binaryop binaryop.4

Function urem binaryop binaryop.5

Function srem binaryop binaryop.6

Function shl binaryop binaryop.7

Function lshr binaryop binaryop.8

Function ashr binaryop binaryop.9

Function and binaryop binaryop.10

Function or binaryop binaryop.11

Function xor binaryop binaryop.12

type cmp2op is toint:int

Function decode(code:cmp2op)seq.word
let i = toint.code
if between(i + 1, 1, 42)then
 let r = ["? Feq Fgt Fge Flt Fle Fne ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? eq ne ugt uge ult ule sgt sge slt sle"_(i + 1)]
 if r ≠ "?"then r else"cmp2op." + toword.i
else"cmp2op." + toword.i

Export toint(cmp2op)int

Export cmp2op(i:int)cmp2op

Export type:cmp2op

Function =(a:cmp2op, b:cmp2op)boolean toint.a = toint.b

Function Feq cmp2op cmp2op.1

Function Fgt cmp2op cmp2op.2

Function Fge cmp2op cmp2op.3

Function Flt cmp2op cmp2op.4

Function Fle cmp2op cmp2op.5

Function Fne cmp2op cmp2op.6

Function eq cmp2op cmp2op.32

Function ne cmp2op cmp2op.33

Function ugt cmp2op cmp2op.34

Function uge cmp2op cmp2op.35

Function ult cmp2op cmp2op.36

Function ule cmp2op cmp2op.37

Function sgt cmp2op cmp2op.38

Function sge cmp2op cmp2op.39

Function slt cmp2op cmp2op.40

Function sle cmp2op cmp2op.41 