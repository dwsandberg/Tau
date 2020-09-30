
module words

use UTF8

use otherseq.alphaword

use otherseq.seq.alphaword

use seq.seq.alphaword

use seq.alphaword

use otherseq.char

use otherseq.int

use encoding.seq.int

use stdlib

use bits

Function type:word internaltype export

type word is record asencoding:encoding.seq.char

Function asencoding(w:word)encoding.seq.char export

Function word(encoding.seq.char)word export

use encoding.seq.char


Function encodeword(a:seq.char)word word.encode( a)

Function decodeword(w:word)seq.char decode( asencoding.w)

Function hash(a:word)int hash.asencoding.a

function assignencoding(l:int, a:seq.char) int toint(bits.assignrandom(l,a) &and  bits(toint( bits.1 << 31)-1))

Function =(a:word, b:word)boolean asencoding.a = asencoding.b

Function ?(a:word, b:word)ordering asencoding.a ? asencoding.b

----

Function merge(a:seq.word)word // make multiple words into a single word. // encodeword.@(+, decodeword, empty:seq.char, a)

* Functions to perform alphabetical sorting

Function type:alphaword internaltype export

type alphaword is record toword:word

Function alphaword(word)alphaword export

Function toword(alphaword)word export

use seq.encodingrep.seq.char

Function addwords(a:encodingstate.seq.char, b:seq.encodingrep.seq.char) encodingstate.seq.char 
 add(a,b)

Function toalphaseq(a:seq.word)seq.alphaword
 // This is just a type change and the compiler recognizes this and does not generate code // @(+, alphaword, empty:seq.alphaword, a)

Function ?(a:alphaword, b:alphaword)ordering
 if toword.a = toword.b then EQ else decodeword.toword.a ? decodeword.toword.b

Function towordseq(a:seq.alphaword)seq.word @(+, toword, empty:seq.word, a)

Function alphasort(a:seq.word)seq.word towordseq.sort.toalphaseq.a

Function ?(a:seq.alphaword, b:seq.alphaword)ordering export

Function alphasort(a:seq.seq.word)seq.seq.word
 let b = @(+, toalphaseq, empty:seq.seq.alphaword, a)
  @(+, towordseq, empty:seq.seq.word, sort.b)

Function checkinteger(w:word)word
 let l = decodeword.w
 let i = if l_1 = char1."-" ∧ length.l > 1 then 2 else 1
  if not.between(toint.l_i, 48, 57)then"WORD"_1 else checkalldigits(l, i)

function checkalldigits(l:seq.char, i:int)word
 if i > length.l then"INTEGER"_1
 else if between(toint.l_i, 48, 57) ∨ l_i = nbspchar then checkalldigits(l, i + 1)
 else"ILLEGAL"_1