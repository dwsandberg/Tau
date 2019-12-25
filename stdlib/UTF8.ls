Module UTF8

use seq.int

use stdlib

use seq.char

type UTF8 is record toseqint:seq.int

/Function UTF8x(s:seq.word)UTF8 UTF8.@(+, decode, empty:seq.int, s)

Function emptyUTF8 UTF8 UTF8.empty:seq.int

Function +(a:UTF8, b:UTF8)UTF8 UTF8(toseqint.a + toseqint.b)

Function +(a:UTF8, ch:char)UTF8  a+toUTF8(ch)

Function =(a:UTF8, b:UTF8)boolean toseqint.a = toseqint.b

Function UTF8(seq.int)UTF8 export

Function UTF8(w:word)UTF8 UTF8.tointseq.decodeword.w

Function toseqint(UTF8)seq.int export

Function commachar char char.44

Function hyphenchar char  char.45

Function periodchar char char.46

Function nbspchar char  // no break space character // char.160



Function toUTF8(n:int)UTF8 
 UTF8.if n < 0 then [ toint.hyphenchar]+ toUTF8(n, 10)else toUTF8(-n, 10)

function toUTF8(n:int, base:int)seq.int 
 // n should always be negative.This is to handle the smallest integer in the twos complement representation of integers // 
  if base + n > 0 then [ 48 - n]else toUTF8(n / base, base)+ [ 48 + n / base * base - n]

Function toUTF8(ch:char)UTF8 
 // convert to UTF8 byte encoding of unicode character // 
  let i=toint.ch
  UTF8.if i < 128 then [ i]else subUTF8(2, i / 64)+ [ 128 + i mod 64]  

function subUTF8(n:int, c:int)seq.int 
 if c < 2^(7 - n)then [ 256 - 2^(8 - n)+ c]else subUTF8(n + 1, c / 64)+ [ 128 + c mod 64]

Function decodeUTF8(b:UTF8)seq.char 
 // converts UTF8 encoded sequence into a sequence of integers(chars)// 
  tocharseq.xx(toseqint.b, 1, empty:seq.int)

function xx(b:seq.int, i:int, result:seq.int)seq.int 
 if i > length.b 
  then result 
  else let x = b_i 
  if x < 128 
  then xx(b, i + 1, result + x)
  else if x < 224 
  then xx(b, i + 2, result +((x - 194)* 64 + b_(i + 1)))
  else if x < 240 
  then xx(b, i + 3, result +((x - 224)* 64^2 +(b_(i + 1) - 128)* 64 + b_(i + 2) - 128))
  else if x < 248 
  then xx(b, i + 4, result +((x - 240)* 64^3 +(b_(i + 1) - 128)* 64^2 +(b_(i + 2) - 128)* 64 + b_(i + 3) - 128))
  else if x < 252 
  then xx(b, i + 5, result +((x - 248)* 64^4 +(b_(i + 1) - 128)* 64^3 +(b_(i + 2) - 128)* 64^2 +(b_(i + 3) - 128)* 64 + b_(i + 4) - 128))
  else xx(b, i + 6, result +((x - 252)* 64^5 +(b_(i + 1) - 128)* 64^4 +(b_(i + 2) - 128)* 64^3 +(b_(i + 3) - 128)* 64^2 +(b_(i + 4) - 128)* 64 + b_(i + 5) - 128))

Function toUTF8(a:seq.word)UTF8 addspace(a, 1, true, emptyUTF8)

function addspace(s:seq.word, i:int, nospace:boolean, result:UTF8)UTF8 
 if i > length.s 
  then result 
  else let this = s_i 
  let single = this in("()-].:&quot_^. "+ space)
  let d = @(+, toUTF8, emptyUTF8, decodeword.this)
  addspace(s, i + 1, single, if nospace ∨ single ∨ this =","_1 then result + d else result + char.32+ d)

