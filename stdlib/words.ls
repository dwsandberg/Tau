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

Export type:word

type word is asencoding:encoding.seq.char

Function wordencodingtoword(i:int)word word.to:encoding.seq.char(i)

Function encodeword(a:seq.char)word{OPTION NOINLINE COMPILETIME}word.encode.a

Function decodeword(w:word)seq.char{OPTION NOINLINE COMPILETIME}decode.asencoding.w

Function hash(a:word)int hash.asencoding.a

Function encoding(w:word)int valueofencoding.asencoding.w

Function assignencoding(a:seq.char)int toint(bits.assignrandom.a ∧ bits(toint(bits.1 << 31) - 1))

Function =(a:word, b:word)boolean{OPTION COMPILETIME}asencoding.a = asencoding.b

Function ?(a:word, b:word)ordering asencoding.a ? asencoding.b

Function ?(a:encodingpair.seq.char, b:encodingpair.seq.char)ordering valueofencoding.code.a ? valueofencoding.code.b

----

Function merge(a:seq.word)word
{OPTION COMPILETIME}
{make multiple words into a single word. }
encodeword.for acc = empty:seq.char, @e ∈ a do acc + decodeword.@e /for(acc)

* Functions to perform alphabetical sorting

Export type:alphaword

type alphaword is toword:word

Export alphaword(word)alphaword

Export toword(alphaword)word

Function toalphaseq(a:seq.word)seq.alphaword
{This is just a type change and the compiler recognizes this and does not generate code}
for acc = empty:seq.alphaword, @e ∈ a do acc + alphaword.@e /for(acc)

Function ?alpha(a:char, b:char)ordering a ? b

Function ?(a:alphaword, b:alphaword)ordering
if toword.a = toword.b then EQ else ?alpha(decodeword.toword.a, decodeword.toword.b)

Function towordseq(a:seq.alphaword)seq.word for acc = empty:seq.word, @e ∈ a do acc + toword.@e /for(acc)

Function alphasort(a:seq.word)seq.word towordseq.sort.toalphaseq.a

Export ?(a:seq.alphaword, b:seq.alphaword)ordering

Function alphasort(a:seq.seq.word)seq.seq.word
let b = for acc = empty:seq.seq.alphaword, @e ∈ a do acc + toalphaseq.@e /for(acc)
for acc = empty:seq.seq.word, @e ∈ sort.b do acc + towordseq.@e /for(acc)

Function checkinteger(w:word)word
let l = decodeword.w
let validdigits = decodeword.first."0123456789" + nbspchar
let validhex = decodeword.first."0123456789ABCDEFabcdef" + nbspchar
if length.l > 2 ∧ l_1 = char1."0" ∧ l_2 ∈ decodeword.first."xX"then
 if for acc = true, @e ∈ l << 2 do acc ∧ binarysearch(validhex, @e) > 0 /for(acc)then
  "INTEGER"_1
 else"ILLEGAL"_1
else
 let i = if length.l > 1 ∧ l_1 = char1."-"then 2 else 1
 if not.between(toint.l_i, 48, 57)then"WORD"_1
 else if for acc = true, @e ∈ l << (i - 1)do acc ∧ binarysearch(validdigits, @e) > 0 /for(acc)then
  "INTEGER"_1
 else"ILLEGAL"_1 