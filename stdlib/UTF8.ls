Module UTF8


use stdlib



use stacktrace



use real

type UTF8 is record toseqint:seq.int

Function type:UTF8 internaltype  export

Function emptyUTF8 UTF8 UTF8.empty:seq.int

Function +(a:UTF8, b:UTF8)UTF8 UTF8(toseqint.a + toseqint.b)

Function +(a:UTF8, ch:char)UTF8  a+encodeUTF8(ch)

Function =(a:UTF8, b:UTF8)boolean toseqint.a = toseqint.b

Function UTF8(seq.int)UTF8 export

Function toseqint(UTF8)seq.int export


Function commachar char char.44

Function hyphenchar char  char.45

Function periodchar char char.46

Function doublequotechar char char.34

Function nbspchar char  // no break space character // char.160



Function toUTF8(n:int)UTF8 
 UTF8.if n < 0 then [ toint.hyphenchar]+ toUTF8(n, 10)else toUTF8(-n, 10)

function toUTF8(n:int, base:int)seq.int 
 // n should always be negative.This is to handle the smallest integer in the twos complement representation of integers // 
  if base + n > 0 then [ 48 - n]else toUTF8(n / base, base)+ [ 48 + n / base * base - n]

Function encodeUTF8(ch:char)UTF8 
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
  let d = @(+, encodeUTF8, emptyUTF8, decodeword.this)
  addspace(s, i + 1, single, if nospace ∨ single ∨ this =","_1 then result + d else result + char.32+ d)
  
  ---------
  
  Function toword(n:int)word 
 // Covert integer to sequence of characters represented as a single word. // 
  encodeword.tocharseq.toseqint.toUTF8.n

/Function print(i:int)seq.word groupdigits.toUTF8.i

/function groupdigits(u:UTF8)seq.word let s = tointseq.u if length.s < 5 ∧(length.s < 4 ∨ s_1 = toint.hyphenchar)then [ encodeword.s]else groupdigits.UTF8.subseq(s, 1, length.s-3)+ [ encodeword.subseq(s, length.s-2, length.s)]

  
  Function toint(w:word)int 
 // Convert an integer represented as a word to an int // cvttoint(decodeword.w, 1, 0)
 
Function intlit(s:UTF8) int   cvttoint(tocharseq.toseqint.s,1,0)

function cvttoint(s:seq.char, i:int, val:int)int 
 if i = 1 ∧ s_1 = hyphenchar 
  then cvttoint(s, i + 1, val)
  else if i > length.s 
  then if s_1 = hyphenchar then-val else val 
  else if s_i = nbspchar 
  then cvttoint(s, i + 1, val)
  else assert between(toint(s_i), 48, 57)report"invalid digit"+ stacktrace 
  cvttoint(s, i + 1, val * 10 + toint(s_i) - 48)

-------------

Function hash(a:seq.char)int hash(tointseq.a)

Function  tointseq(a:seq.char) seq.int  
// This is just a type change and the compiler recognizes this and does not generate code // 
  @(+, toint , empty:seq.int, a)


Function  tocharseq(a:seq.int) seq.char // builtin.NOOP //
// This is just a type change and the compiler recognizes this and does not generate code // 
  @(+, char, empty:seq.char, a)


_________________


Function print( decimals:int,rin1:real)seq.word 
 let neg= rin1 ? toreal.0 = LT  
 let rin=if neg then toreal.0 - rin1 else rin1
 let a = 10^decimals 
  let r = rin + 1.0 / toreal(a * 2)
  let r2=  if decimals > 0 
   then  [ toword.intpart.r ,"."_1, encodeword(tocharseq.toseqint.lpad(toseqint.toUTF8.intpart((r - toreal.intpart.r)* toreal.a), decimals))]
   else  [ toword.intpart.r] 
   if neg then "-"+r2 else r2 


Function toUTF8(rin:real, decimals:int) UTF8
 if rin ? toreal.0 = LT 
  then   encodeUTF8.hyphenchar + toUTF8(toreal.0 - rin, decimals)
  else let a = 10^decimals 
  let r = rin + 1.0 / toreal(a * 2)
    if decimals > 0 
   then toUTF8.intpart.r +encodeUTF8.periodchar+ lpad(toseqint.toUTF8.intpart((r - toreal.intpart.r)* toreal.a), decimals)
   else toUTF8.intpart.r 


Function reallit(s:UTF8)real reallit(toseqint.s,-1, 1, 0, 1)


function reallit(s:seq.int, decimals:int, i:int, val:int, neg:int)real 
 if i > length.s 
  then let r = if decimals < 1 then toreal.val  else makereal(val,decimals) 
   if neg < 1 then-(1.0 * r)else r 
  else if between(s_i, 48, 57)
  then reallit(s, if decimals =-1 then-1 else decimals + 1, i + 1, 10 * val + s_i - 48, neg)
  else if s_i = 32 ∨ s_i = toint.commachar 
  then reallit(s, decimals, i + 1, val, neg)
  else if i < 3 ∧ s_i = toint.hyphenchar 
  then reallit(s, decimals, i + 1, val,-1)
  else if i < 3 ∧ s_i = toint.(decodeword."+"_1 )_1
  then reallit(s, decimals, i + 1, val,1)
  else assert s_i = toint.periodchar report"unexpected character in real literal"+ encodeword.tocharseq.s 
  reallit(s, decimals + 1, i + 1, val, neg)

Function lpad(l:seq.int, n:int) UTF8 UTF8(constantseq(n - length.l, 48)+ l)

