module words

use UTF8

use bits

use standard

use otherseq.alphaword

use otherseq.char

use seq.char

use otherseq.int

use otherseq.seq.alphaword

use encoding.seq.char

use seq.encodingpair.seq.char

/use encoding.seq.int

Export type:word

type word is record asencoding:encoding.seq.char

Function wordencodingtoword(i:int)word word.to:encoding.seq.char(i)

Function encodeword(a:seq.char)word word.encode.a

Function decodeword(w:word)seq.char decode.asencoding.w

Function hash(a:word)int hash.asencoding.a

Function encoding(w:word)int valueofencoding.asencoding.w

function assignencoding(l:int, a:seq.char)int
 toint(bits.assignrandom(l, a) ∧ bits(toint(bits.1 << 31) - 1))

Function =(a:word, b:word)boolean asencoding.a = asencoding.b

Function ?(a:word, b:word)ordering asencoding.a ? asencoding.b

----

Function merge(a:seq.word)word
 \\ make multiple words into a single word. \\
 encodeword.for @e ∈ a, acc = empty:seq.char ; acc + decodeword.@e

* Functions to perform alphabetical sorting

Export type:alphaword s

type alphaword is record toword:word

Export alphaword(word)alphaword

Export toword(alphaword)word

Function toalphaseq(a:seq.word)seq.alphaword
 \\ This is just a type change and the compiler recognizes this and does not generate code \\
 for @e ∈ a, acc = empty:seq.alphaword ; acc + alphaword.@e

Function ?alpha(a:char, b:char)ordering a ? b

Function ?(a:alphaword, b:alphaword)ordering
 if toword.a = toword.b then EQ else ?alpha(decodeword.toword.a, decodeword.toword.b)

Function towordseq(a:seq.alphaword)seq.word for @e ∈ a, acc = empty:seq.word ; acc + toword.@e

Function alphasort(a:seq.word)seq.word towordseq.sort.toalphaseq.a

Export ?(a:seq.alphaword, b:seq.alphaword)ordering

Function alphasort(a:seq.seq.word)seq.seq.word
 let b = for @e ∈ a, acc = empty:seq.seq.alphaword ; acc + toalphaseq.@e
  for @e ∈ sort.b, acc = empty:seq.seq.word ; acc + towordseq.@e

Function checkinteger(w:word)word
 let l = decodeword.w
 let validdigits = decodeword.first."0123456789" + nbspchar
 let validhex = decodeword.first."0123456789ABCDEFabcdef" + nbspchar
  if length.l > 2 ∧ l_1 = char1."0"
  ∧ l_2 ∈ decodeword.first."xX"then
  if for @e ∈ l << 2, acc = true ; acc ∧ binarysearch(validhex, @e) > 0 then
   "INTEGER"_1
   else"ILLEGAL"_1
  else
   let i = if length.l > 1 ∧ l_1 = char1."-"then 2 else 1
    if not.between(toint.l_i, 48, 57)then"WORD"_1
    else if for @e ∈ l << (i - 1), acc = true ; acc ∧ binarysearch(validdigits, @e) > 0 then
    "INTEGER"_1
    else"ILLEGAL"_1