Module words

use UTF8

use otherseq.alphaword

use otherseq.alphawords

use otherseq.char

use encoding.seq.char

use standard

use xxhash

Export type:alphaword

Export toword(alphaword) word

Export type:word

Export alphaword(word) alphaword

Export asencoding(w:word) encoding.seq.char

Export >1(a:seq.alphaword, b:seq.alphaword) ordering {From otherseq.alphaword}

type word is asencoding:encoding.seq.char

Function hash(a:seq.char) int
finalmix32.for acc = hashstart32.0, @e ∈ tointseq.a do hash32(acc, @e) /for (acc)

Function wordencodingtoword(i:int) word word.to:encoding.seq.char(i)

Function encodeword(a:seq.char) word {OPTION NOINLINE COMPILETIME} word.encode.a

Function decodeword(w:word) seq.char {OPTION NOINLINE COMPILETIME} decode.asencoding.w

Function hash(a:word) int hash.asencoding.a

Function =(a:word, b:word) boolean {OPTION COMPILETIME} asencoding.a = asencoding.b

Function >1(a:word, b:word) ordering asencoding.a >1 asencoding.b

Function merge(a:seq.word) word
{OPTION COMPILETIME}
{make multiple words into a single word. }
encodeword.for acc = empty:seq.char, @e ∈ a do acc + decodeword.@e /for (acc)

* Functions to perform alphabetical sorting

type alphaword is toword:word

Function toalphaseq(a:seq.word) seq.alphaword
{This is just a type change and the compiler recognizes this and does not generate code}
for acc = empty:seq.alphaword, @e ∈ a do acc + alphaword.@e /for (acc)

Function ?alpha(a:char, b:char) ordering a >1 b

Function >1(a:alphaword, b:alphaword) ordering
if toword.a = toword.b then EQ else ?alpha(decodeword.toword.a, decodeword.toword.b)

Function towordseq(a:seq.alphaword) seq.word
for acc = empty:seq.word, @e ∈ a do acc + toword.@e /for (acc)

Function alphasort(a:seq.word) seq.word towordseq.sort.toalphaseq.a

type alphawords is toseq:seq.alphaword

function ?alpha(a:alphaword, b:alphaword) ordering a >1 b

function >1(a:alphawords, b:alphawords) ordering ?alpha(toseq.a, toseq.b)

Function alphasort(a:seq.seq.word) seq.seq.word
for acc = empty:seq.alphawords, s ∈ a do
 acc + alphawords.toalphaseq.s
/for (for acc2 = empty:seq.seq.word, s2 ∈ sort.acc do acc2 + towordseq.toseq.s2 /for (acc2))

Function checkinteger(w:word) word
let l = decodeword.w
let validdigits = decodeword.first."0123456789" + nbspchar
let validhex = decodeword.first."0123456789ABCDEFabcdef" + nbspchar
if length.l > 2 ∧ l_1 = char1."0" ∧ l_2 ∈ decodeword.first."xX" then
 if for acc = true, @e ∈ l << 2 do acc ∧ binarysearch(validhex, @e) > 0 /for (acc) then
  "INTEGER"_1
 else
  "ILLEGAL"_1
else
 let i = if length.l > 1 ∧ l_1 = char1."-" then 2 else 1
 if not.between(toint.l_i, 48, 57) then
  "WORD"_1
 else if for acc = true, @e ∈ l << (i - 1) do
  acc ∧ binarysearch(validdigits, @e) > 0
 /for (acc) then
  "INTEGER"_1
 else
  "ILLEGAL"_1 