module words

use UTF8

use otherseq.alphaword

use otherseq.seq.alphaword

use seq.seq.alphaword

use seq.alphaword

use bits

use otherseq.char

use encoding.seq.char

use seq.encodingpair.seq.char

use otherseq.int

use encoding.seq.int

use standard

Export type:word s

type word is record asencoding:encoding.seq.char

Export asencoding(w:word)encoding.seq.char

Export word(encoding.seq.char)word

Function encodeword(a:seq.char)word word.encode.a

Function decodeword(w:word)seq.char decode.asencoding.w

Function hash(a:word)int hash.asencoding.a

function assignencoding(l:int, a:seq.char)int
 toint(bits.assignrandom(l, a) ∧ bits(toint(bits.1 << 31) - 1))

Function =(a:word, b:word)boolean asencoding.a = asencoding.b

Function ?(a:word, b:word)ordering asencoding.a ? asencoding.b

----

Function merge(a:seq.word)word
 // make multiple words into a single word. // encodeword(a @ +(empty:seq.char, decodeword.@e))

* Functions to perform alphabetical sorting

Export type:alphaword s

type alphaword is record toword:word

Export alphaword(word)alphaword

Export toword(alphaword)word

Function addwords(b:seq.encodingpair.seq.char)encodingstate.seq.char addencodingpairs.b

Function toalphaseq(a:seq.word)seq.alphaword
 // This is just a type change and the compiler recognizes this and does not generate code //
 a @ +(empty:seq.alphaword, alphaword.@e)

Function ?(a:alphaword, b:alphaword)ordering
 if toword.a = toword.b then EQ else decodeword.toword.a ? decodeword.toword.b

Function towordseq(a:seq.alphaword)seq.word a @ +(empty:seq.word, toword.@e)

Function alphasort(a:seq.word)seq.word towordseq.sort.toalphaseq.a

Export ?(a:seq.alphaword, b:seq.alphaword)ordering

Function alphasort(a:seq.seq.word)seq.seq.word
 let b = a @ +(empty:seq.seq.alphaword, toalphaseq.@e)
  sort.b @ +(empty:seq.seq.word, towordseq.@e)

Function checkinteger(w:word)word
 let l = decodeword.w
 let i = if l_1 = char1."-" ∧ length.l > 1 then 2 else 1
  if not.between(toint.l_i, 48, 57)then"WORD"_1 else checkalldigits(l, i)

function checkalldigits(l:seq.char, i:int)word
 if i > length.l then"INTEGER"_1
 else if between(toint.l_i, 48, 57) ∨ l_i = nbspchar then checkalldigits(l, i + 1)
 else"ILLEGAL"_1