#!/usr/local/bin/tau

 

module words

use stdlib

use encoding.seq.int

use seq.char

use seq.alphaword

use otherseq.alphaword

use otherseq.int

use otherseq.char

use otherseq.seq.alphaword

use seq.alphaword



use seq.seq.alphaword



use UTF8

use words

Function type:word  internaltype  export


type wordencoding is encoding seq.char

Function wordencoding erecord.seq.char export

type word is record asencoding:encoding.seq.char

Function asencoding(w:word) encoding.seq.char export

Function word(encoding.seq.char) word export

Function add(erecord.seq.char,seq.encodingrep.seq.char) int export

Function encodeword(a:seq.char)word  word.encode(wordencoding,a)

Function decodeword(w:word)seq.char decode( wordencoding,asencoding.w)

Function hash(a:word)int hash.asencoding.a

Function =(a:word, b:word)boolean asencoding.a = asencoding.b

Function ?(a:word, b:word)ordering asencoding.a ? asencoding.b

Function merge(a:seq.word)word 
 // make multiple words into a single word. // encodeword.@(+, decodeword, empty:seq.char, a)

* Functions to perform alphabetical sorting

Function type:alphaword internaltype export


type alphaword is record toword:word

Function alphaword(word)alphaword export

Function toword(alphaword)word export

Function toalphaseq(a:seq.word)seq.alphaword 
 // This is just a type change and the compiler recognizes this and does not generate code // 
  @(+, alphaword, empty:seq.alphaword, a)

Function ?(a:alphaword, b:alphaword)ordering 
 if toword.a = toword.b then EQ else decodeword.toword.a ? decodeword.toword.b

Function towordseq(a:seq.alphaword)seq.word @(+, toword, empty:seq.word, a)

Function alphasort(a:seq.word)seq.word towordseq.sort.toalphaseq.a

Function ?(a:seq.alphaword, b: seq.alphaword)ordering export

use seq.seq.alphaword

Function alphasort(a:seq.seq.word)seq.seq.word 
 let b = @(+, toalphaseq, empty:seq.seq.alphaword, a)
  @(+, towordseq, empty:seq.seq.word, sort.b)

