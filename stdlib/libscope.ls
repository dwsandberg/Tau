Module mytype

use stdlib

Function type:mytype internaltype export

type mytype is record towords:seq.word

Function mytype(seq.word)mytype export

Function towords(mytype)seq.word export


Function print(p:mytype)seq.word prt(towords.p, length.towords.p)

function prt(s:seq.word, i:int)seq.word
 if i = 1 then [ s_1]
 else [ s_i] + "." + prt(s, i - 1)

Function =(t:mytype, b:mytype)boolean towords.t = towords.b

Function abstracttype(m:mytype)word(towords.m)_(length.towords.m)

Function parameter(m:mytype)mytype mytype.subseq(towords.m, 1, length.towords.m - 1)

Function isabstract(a:mytype)boolean(towords.a)_1 = "T"_1

Function isinstance(a:mytype)boolean length.towords.a > 1 ∧ not(parameter.a = mytype."T")

Function iscomplex(a:mytype)boolean length.towords.a > 1

Function replaceT(with:mytype, m:mytype)mytype
 if(towords.m)_1 = "T"_1 then
 mytype(towords.with + subseq(towords.m, 2, length.towords.m))
 else m

Module libscope

use mytype

use encoding.seq.char

use seq.encodingrep.seq.char

use seq.liblib

use seq.libmod



use seq.mytype

use stdlib

use seq.seq.word

use seq.word



Function type:liblib internaltype export


Function type:libmod internaltype export



type liblib is record libname:seq.word, words:seq.encodingrep.seq.char, mods:seq.libmod, timestamp:int, readonly:boolean

Function liblib(a:seq.word, d:seq.libmod)liblib liblib(a, empty:seq.encodingrep.seq.char, d, 0, false)

Function timestamp(liblib)int export

Function libname(liblib)seq.word export

Function mods(liblib)seq.libmod export

Function words(liblib)seq.encodingrep.seq.char export

Function readonly(liblib)boolean export


use otherseq.word


function =(a:libmod, b:libmod)boolean modname.a = modname.b

Function uses(libmod)seq.mytype export

Function loadedlibs seq.liblib builtin.usemangle


type libmod is record parameterized:boolean, modnamex:word, defines:seq.symbol, exports:seq.symbol, uses:seq.mytype

Function libmod(parameterized:boolean, modname:word, defines:seq.symbol, exports:seq.symbol, uses:seq.mytype)libmod export

Function libmod(modname:mytype, defines:seq.symbol, exports:seq.symbol, uses:seq.mytype)libmod 
 libmod(isabstract.modname,abstracttype.modname,defines,exports,uses)
 
Function modname(l:libmod)mytype  mytype.if parameterized.l then  "T"+modnamex.l else [modnamex.l]


Function defines(l:libmod)seq.symbol export

Function exports(l:libmod)seq.symbol export





type symbol is record  fsig:seq.word,module:seq.word,returntype:seq.word, zcode:seq.symbol,instruction:seq.word

use seq.symbol

Function symbol(fsig:seq.word,module:seq.word,returntype:seq.word, zcode:seq.symbol) symbol 
symbol(fsig,module,returntype,zcode,"")

function symbol(fsig:seq.word,module:seq.word,returntype:seq.word, zcode:seq.symbol,instruction:seq.word) symbol 
export

Function fsig(symbol)seq.word export

Function module(symbol)seq.word export

Function returntype(symbol)seq.word export

Function type:symbol internaltype export

Function zcode(symbol)seq.symbol export

Function instruction(symbol)seq.word export

type myinternaltype is record size:int,kind:word,name:word,modname:mytype,subflds:seq.mytype

function myinternaltype(size:int,kind:word,name:word,modname:mytype,subflds:seq.mytype) myinternaltype
export

Function type:myinternaltype internaltype export

Function size(myinternaltype)int export

Function kind(myinternaltype)word export

Function name(myinternaltype)word export

Function modname(myinternaltype)mytype export

Function subflds(myinternaltype)seq.mytype export

module mangle

use bits

use seq.char

use stdlib

use seq.word

Function mangle2(name: seq.word,modname:seq.word, parameters:seq.seq.word) word
 encodeword.@(seperator.char.charmajorseparator,codeup,empty:seq.char, [[merge.name],modname]+parameters)

function seperator( sep:char,acc:seq.char,b:seq.char) seq.char
if isempty.acc then b else acc+sep+b 


Function codedown(w:word)seq.seq.word codedown(decodeword.w, 1, empty:seq.char,"", empty:seq.seq.word)

Function changeit boolean false

function codedown(l:seq.char, i:int, w:seq.char, words:seq.word, result:seq.seq.word)seq.seq.word
 if i > length.l then
 let a = if isempty.w then words else words + encodeword.w
   if isempty.a then result else result + a
 else if l_i = char.charminorseparator then
 codedown(l, i + 1, empty:seq.char, words + encodeword.w, result)
 else if l_i = char.charmajorseparator then
 codedown(l, i + 1, empty:seq.char,"", result + (words + encodeword.w))
 else if l_i = char1."Q"then
 assert i + 2 ≤ length.l report"format problem with codedown for" + encodeword.l
  let first = hexvalue.l_(i + 1)
  let inc=if first > 0 then // one hex digit // 3 else // two hex digit // 6
  let t = first * 16 + hexvalue.l_(i + 2)
   let ch=if inc=3 then  char.t  
   else
    char(((t * 16 + hexvalue.l_(i + 3)) * 16 + hexvalue.l_(i + 4))
    * 16
    + hexvalue.l_(i + 5))
    if  changeit &and  ch in decodeword.".:"_1   then 
      codedown(l, i + 1, empty:seq.char, words + encodeword.w+encodeword.[ch], result)
    else 
     codedown(l, i + inc, w + ch, words, result)
 else codedown(l, i + 1, w + l_i, words, result)

function legal seq.char decodeword."0123456789ABCDEFGHIJKLMNOPRSTUVWXYabcdefghijklmnopqrstuvwxy"_1

function hexvalue(c:char)int
 let i = toint.c
  if between(i, 48, 57)then i - 48 else i - 65 + 10

function codeup(s:seq.word)seq.char @(addword, identity, empty:seq.char, s)

function addword(s:seq.char, w:word)seq.char
 // adds minor separator between words //
 @(codeup, identity, if isempty.s then s else s + char.charminorseparator, decodeword.w)

function charmajorseparator int // Z // 90

function charminorseparator int // z // 122

function codeup(l:seq.char, char:char)seq.char
 // represent legal characters as themselves, and others as Qxx where xx is hexadecimal of byte or Q0xxxx //
 let charQ = char.81
  if char in legal then l + char
  else if toint.char < 256 then @(+, hexdigit.bits.toint.char, l + charQ, [ 1, 0])
  else @(+, hexdigit.bits.toint.char, l + charQ, [ 4, 3, 2, 1, 0])

function hexdigit(val:bits, digit:int)char legal_(toint(val >> 4 * digit ∧ bits.15) + 1)

Function manglednopara(w:word)int @(+, count.char.90, -1, decodeword.w)

function count(val:char, i:char)int if val = i then 1 else 0


