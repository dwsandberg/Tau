module mangle

use bits

use standard

use seq.char

use otherseq.word

use seq.seq.word

Function printmangled(w:word)seq.word
let d = codedown.w
let para = for acc ="", e = d << 2 do
 if acc = ""then printtype.e else acc + "," + printtype.e
/for(acc)
d_1
 + if isempty.para then""else"(" + para + ")"/if
 + if length.d > 1 then" /keyword module:" + printtype.d_2 else""

function printtype(a:seq.word)seq.word
 for acc ="", e = a do
  if acc = ""then acc + e else [ e] + "." + acc
 /for(acc)

Function mangle(fsig:seq.word, module:seq.word)word
let i = findindex("("_1, fsig)
let modname = module
let parameters = break(","_1,"", subseq(fsig, i + 1, length.fsig - 1))
encodeword.for acc = empty:seq.char, @e = [ [ merge.subseq(fsig, 1, i - 1)], module] + parameters do
  if isempty.acc then codeup.@e else acc + char.charmajorseparator + codeup.@e
 /for(acc)

Function codedown(w:word)seq.seq.word codedown(decodeword.w, 1, empty:seq.char,"", empty:seq.seq.word)

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
  let inc = if first > 0 then { one hex digit }3 else { two hex digit }6
  let t = first * 16 + hexvalue.l_(i + 2)
  let ch = if inc = 3 then char.t
  else
   char(((t * 16 + hexvalue.l_(i + 3)) * 16 + hexvalue.l_(i + 4))
   * 16
   + hexvalue.l_(i + 5))
  if ch ∈ decodeword.".:"_1 then
    codedown(l, i + 1, empty:seq.char, words + encodeword.w + encodeword.[ ch], result)
   else codedown(l, i + inc, w + ch, words, result)
 else codedown(l, i + 1, w + l_i, words, result)

function legal seq.char decodeword."0123456789ABCDEFGHIJKLMNOPRSTUVWXYabcdefghijklmnopqrstuvwxy"_1

function hexvalue(c:char)int
let i = toint.c
 if between(i, 48, 57)then i - 48 else i - 65 + 10

function codeup(s:seq.word)seq.char
 for acc = empty:seq.char, @e = s do addword(acc, @e)/for(acc)

function addword(s:seq.char, w:word)seq.char
 { adds minor separator between words }
 for acc = if isempty.s then s else s + char.charminorseparator /if, @e = decodeword.w do
  codeup(acc, @e)
 /for(acc)

function charmajorseparator int { Z }90

function charminorseparator int { z }122

function codeup(l:seq.char, char:char)seq.char
 { represent legal characters as themselves, and others as Qxx where xx is hexadecimal of byte or Q0xxxx }
 let charQ = char.81
  if char ∈ legal then l + char
  else if toint.char < 256 then
   for acc = l + charQ, @e = [ 1, 0]do acc + hexdigit(bits.toint.char, @e)/for(acc)
  else
   for acc = l + charQ, @e = [ 4, 3, 2, 1, 0]do
    acc + hexdigit(bits.toint.char, @e)
   /for(acc)

function hexdigit(val:bits, digit:int)char legal_(toint(val >> (4 * digit) ∧ bits.15) + 1)

Function manglednopara(w:word)int
 for acc =-1, @e = decodeword.w do acc + count(char.90, @e)/for(acc)

function count(val:char, i:char)int if val = i then 1 else 0 