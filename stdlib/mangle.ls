module mangle

use bits

use seq.char

use stdlib

use seq.word

function seperator(sep:char, acc:seq.char, b:seq.char)seq.char
 if isempty.acc then b else acc + sep + b

Function break(w:word, a:seq.word, j:int)seq.seq.word
 let i = findindex(w, a, j)
  if i > length.a then
  if j > length.a then empty:seq.seq.word else [ subseq(a, j, i)]
  else [ subseq(a, j, i - 1)] + break(w, a, i + 1)

Function mangle(fsig:seq.word, module:seq.word)word
 let i = findindex("("_1, fsig)
 let modname = module
 let parameters = break(","_1, subseq(fsig, 1, length.fsig - 1), i + 1)
  encodeword
  .@(seperator.char.charmajorseparator, codeup, empty:seq.char, [ [ merge.subseq(fsig, 1, i - 1)], module] + parameters)

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
  let inc = if first > 0 then // one hex digit // 3 else // two hex digit // 6
  let t = first * 16 + hexvalue.l_(i + 2)
  let ch = if inc = 3 then char.t
  else
   char(((t * 16 + hexvalue.l_(i + 3)) * 16 + hexvalue.l_(i + 4))
   * 16
   + hexvalue.l_(i + 5))
   if ch in decodeword.".:"_1 then
   codedown(l, i + 1, empty:seq.char, words + encodeword.w + encodeword.[ ch], result)
   else codedown(l, i + inc, w + ch, words, result)
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

Function manglednopara(w:word)int @(+, count.char.90,-1, decodeword.w)

function count(val:char, i:char)int if val = i then 1 else 0