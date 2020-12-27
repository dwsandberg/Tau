Module UTF8

use otherseq.int

use real

use standard

use xxhash

use seq.byte

use bits

type UTF8 is record toseqbyte:seq.byte

Function length(a:UTF8)  int length.toseqbyte.a

Function _(a:UTF8,i:int) byte  (toseqbyte.a)_i
 
Export type:UTF8

Export UTF8(seq.byte) UTF8

Export toseqbyte(UTF8) seq.byte

Function emptyUTF8 UTF8 UTF8.empty:seq.int

Function +(a:UTF8, b:UTF8)UTF8 UTF8(toseqbyte.a + toseqbyte.b)

Function +(a:UTF8, ch:char)UTF8 a + encodeUTF8.ch

Function =(a:UTF8, b:UTF8)boolean toseqbyte.a = toseqbyte.b

Function  UTF8(s:seq.int)UTF8   UTF8(s @ +(empty:seq.byte,byte.@e))


Function commachar char char.44

Function hyphenchar char char.45

Function periodchar char char.46

Function doublequotechar char char.34

Function nbspchar char // no break space character // char.160

Function toUTF8(n:int)UTF8
 UTF8.if n < 0 then [ toint.hyphenchar] + toUTF8(n, 10)else toUTF8(-n, 10)

function toUTF8(n:int, base:int)seq.int
 // n should always be negative.This is to handle the smallest integer in the twos complement representation of integers //
 if base + n > 0 then [ 48 - n]
 else
  toUTF8(n / base, base) + [ 48 + n / base * base - n]

Function encodeUTF8(ch:char)UTF8
 // convert to UTF8 byte encoding of unicode character //
 let i = toint.ch
  UTF8
  .if i < 128 then [ i]
  else subUTF8(2, i / 64) + [ 128 + i mod 64]

function subUTF8(n:int, c:int)seq.int
 if c < 2^(7 - n)then [ 256 - 2^(8 - n) + c]
 else subUTF8(n + 1, c / 64) + [ 128 + c mod 64]

Function decodeUTF8(b:UTF8)seq.char
 // converts UTF8 encoded sequence into a sequence of integers(chars)// 
 decodeUTF8(b,1,length.b)
 
 
Function decodeUTF8(a:UTF8,start:int,end:int) seq.char 
tocharseq.xx(toseqbyte.a,max(1,start),min(end,length.toseqbyte.a),empty:seq.int)

 


function xx(b:seq.byte, i:int, end:int, result:seq.int)seq.int
 if i > end then result
 else
  let x = toint.b_i
   if x < 128 then xx(b, i + 1, end, result + x)
   else if x < 224 then
   xx(b, i + 2, end, result + ((x - 194) * 64 + toint.b_(i + 1)))
   else if x < 240 then
   xx(b, i + 3, end, result
    + ((x - 224) * 64^2 + (toint.b_(i + 1) - 128) * 64
    + toint.b_(i + 2)
    - 128))
   else if x < 248 then
   xx(b, i + 4, end,result
    + ((x - 240) * 64^3 + (toint.b_(i + 1) - 128) * 64^2
    + (toint.b_(i + 2) - 128) * 64
    + toint.b_(i + 3)
    - 128))
   else if x < 252 then
   xx(b, i + 5, end, result
    + ((x - 248) * 64^4 + (toint.b_(i + 1) - 128) * 64^3
    + (toint.b_(i + 2) - 128) * 64^2
    + (toint.b_(i + 3) - 128) * 64
    + toint.b_(i + 4)
    - 128))
   else
    xx(b, i + 6,end, result
    + ((x - 252) * 64^5 + (toint.b_(i + 1) - 128) * 64^4
    + (toint.b_(i + 2) - 128) * 64^3
    + (toint.b_(i + 3) - 128) * 64^2
    + (toint.b_(i + 4) - 128) * 64
    + toint.b_(i + 5)
    - 128))

Function toUTF8(a:seq.word)UTF8 addspace(a, 1, true, emptyUTF8)

function addspace(s:seq.word, i:int, nospace:boolean, result:UTF8)UTF8
 // nospace means add no space before word s_i.comma adds space after but not before single means add no space before or after //
 if i > length.s then result
 else
  let this = s_i
   if this = " &br"_1 then addspace(s, i + 1, true, result + char.10)
   else if this = ","_1 then
   // no space before but space after // addspace(s, i + 1, false, result + char1.",")
   else
    let d = decodeword.this @ +(emptyUTF8, encodeUTF8.@e)
     if this ∈ ('-()].:"_^. ' + space)then
     // no space before or after // addspace(s, i + 1, true, result + d)
     else
      addspace(s, i + 1, false, if nospace then result + d else result + char.32 + d)

---------

Function toword(n:int)word // Covert integer to sequence of characters represented as a single word. // 
encodeword.decodeUTF8.toUTF8.n

/Function print(i:int)seq.word groupdigits.toUTF8.i

/function groupdigits(u:UTF8)seq.word let s = tointseq.u if length.s < 5 ∧(length.s < 4 ∨ s_1 = toint.hyphenchar)then [ encodeword.s]else groupdigits.UTF8.subseq(s, 1, length.s-3)+ [ encodeword.subseq(s, length.s-2, length.s)]

Function toint(w:word)int // Convert an integer represented as a word to an int // cvttoint.decodeword.w 

Function intlit(s:UTF8)int cvttoint.decodeUTF8.s 

Function cvttoint(s:seq.char) int
   // Hex values starting with 0x or 0X are allowed. //
       if length.s > 2 &and s_2 &in decodeword.first."Xx" then
         toint( s @ hexdigit(0x0, @e))
       else 
         let val=s @ decimaldigit(0, @e) 
         // Since there are more negative numbers in twos-complement we calculate using negative values. //  
          if val=0 &or s_1=char1."-" then  val else -val
         

function hexdigit(b:bits, c:char)bits 
    let validhex=decodeword.first."0123456789ABCDEFabcdef" 
       let i0 = binarysearch(validhex,c) 
       let i=if i0 > 16 then i0-6 else i0
        if i > 0 then ( b << 4 )∨ bits(i-1) 
        else assert  c &in [char1."x",char1."X",nbspchar] report"invalid hex digit"+ encodeword.[c ] 
         b 
       
       
function decimaldigit(val:int, c:char)int
    let validdigits = decodeword.first."0123456789" 
        let i = binarysearch(validdigits,c)
         if i > 0 then ( val * 10 ) - (i-1)   
        else assert c &in [char1."-", nbspchar] report "invalid   digit" + encodeword.[c ] 
        val
        
use bits

use otherseq.char

use seq.char
        
-------------

Function hash(a:seq.char)int
 if a = decodeword."//"_1 then hash.tointseq.a
 else finalmix32(tointseq.a @ hash32(hashstart32.0, @e))

Function tointseq(a:seq.char)seq.int
 // This is just a type change and the compiler recognizes this and does not generate code //
 a @ +(empty:seq.int, toint.@e)

Function tocharseq(a:seq.int)seq.char
 // builtin.NOOP //
 // This is just a type change and the compiler recognizes this and does not generate code //
 a @ +(empty:seq.char, char.@e)

_________________

Function print(decimals:int, rin1:real)seq.word
 let neg =(rin1 ? toreal.0) = LT
 let rin = if neg then toreal.0 - rin1 else rin1
 let a = 10^decimals
 let r = rin + 1.0 / toreal(a * 2)
 let r2 = if decimals > 0 then
 [ toword.intpart.r,"."_1, encodeword.lpad(decimals, char.48, decodeUTF8.toUTF8.intpart((r - toreal.intpart.r) * toreal.a))]
 else [ toword.intpart.r]
  if neg then"-" + r2 else r2

Function toUTF8(rin:real, decimals:int)UTF8
 if(rin ? toreal.0) = LT then encodeUTF8.hyphenchar + toUTF8(toreal.0 - rin, decimals)
 else
  let a = 10^decimals
  let r = rin + 1.0 / toreal(a * 2)
   if decimals > 0 then
   toUTF8.intpart.r + encodeUTF8.periodchar
    + UTF8.lpad(decimals, byte.48, toseqbyte.toUTF8.intpart((r - toreal.intpart.r) * toreal.a))
   else toUTF8.intpart.r

Function reallit(s:UTF8)real reallit(decodeUTF8.s,-1, 1, 0, 1)

Function makereal(w:seq.word)real reallit(w @ +(empty:seq.char, decodeword.@e),-1, 1, 0, 1)

use otherseq.byte

function reallit(s:seq.char, decimals:int, i:int, val:int, neg:int)real
 if i > length.s then
 let r = if decimals < 1 then toreal.val else toreal.val / toreal.decimals
   if neg < 1 then-1.0 * r else r
 else if between(toint.s_i, 48, 57)then
 reallit(s, if decimals = -1 then-1 else decimals * 10, i + 1, 10 * val + toint.s_i - 48, neg)
 else if s_i = char.32 ∨ s_i = commachar then
 reallit(s, decimals, i + 1, val, neg)
 else if i < 3 ∧ s_i = hyphenchar then reallit(s, decimals, i + 1, val,-1)
 else if i < 3 ∧ s_i = char1."+"then
 reallit(s, decimals, i + 1, val, 1)
 else
  assert s_i = periodchar report"unexpected character in real literal" + encodeword.s
   reallit(s, 1, i + 1, val, neg)