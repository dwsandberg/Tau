Module test2

Count word frequence in text file. An indexed encoding is used to assign indexes to each distinct word in the 
 file. Uses a dseq to provide a 0 count for words that have not yet been encountered and assigned an index 
 . 

run test2 test2

use encoding.indexedword

use fileio

use oseq.wordfreq

use seq.seq.word

use seq.word

use seq.wordfreq

use stdlib

use textio

type indexedword is record w:word, index:int

function addindex(a:indexedword, i:int)indexedword indexedword(w.a, i)

type eword is encoding indexedword

function hash(a:indexedword)int hash.w.a

function =(a:indexedword, b:indexedword)boolean w.a = w.b

type wordfreq is record count:int, w:word

function =(a:wordfreq, b:wordfreq)boolean false

function ?(a:wordfreq, b:wordfreq)ordering count.a ? count.b

function count(s:seq.wordfreq, w:word)seq.wordfreq 
 replace(s, findindex(eword, indexedword(w, 0)), wordfreq(count.s_findindex(eword, indexedword(w, 0))+ 1, w))

function print(p:wordfreq)seq.word 
 if count.p = 0 
  then empty:seq.word 
  else"&br the word"+ w.p +"occurs"+ toword.count.p +"times."+ EOL

function removelowcount(mincount:int, p:wordfreq)seq.wordfreq 
 if count.p < mincount then empty:seq.wordfreq else [ p]

function wordfreq(mincount:int, a:seq.seq.word)seq.wordfreq 
 sort.@(+, removelowcount(mincount), empty:seq.wordfreq, @(count, identity, dseq.wordfreq(0,"A"_1), a))

Function test2 seq.word @(+, print, empty:seq.word, wordfreq(300, gettext."testall/input"))

function count(s:seq.wordfreq, w:seq.word)seq.wordfreq @(count, identity, s, w)

