#!/usr/local/bin/tau ; use test2 ; test2

Module wordfreq

Count word frequence in text file. An indexed encoding is used to assign indexes to each distinct word in the file. Uses a dseq to provide a 0 count for words that have not yet been encountered and assigned an index. 

use fileio

use standard

use textio

use encoding.indexedword

use otherseq.wordfreq

use seq.wordfreq

use sparseseq.wordfreq

use seq.seq.word

type indexedword is record w:word

Function assignencoding(length:int, data:indexedword)int length + 1

function hash(a:indexedword)int hash.w.a

function =(a:indexedword, b:indexedword)boolean w.a = w.b

type wordfreq is record count:int, w:word

function =(a:wordfreq, b:wordfreq)boolean false

function ?(a:wordfreq, b:wordfreq)ordering count.a ? count.b

function count(s:seq.wordfreq, w:word)seq.wordfreq
 let index = valueofencoding.encode.indexedword.w
  replaceS(s, index, [wordfreq(count.s_index + 1, w)])

function print(p:wordfreq)seq.word
 if count.p = 0 then empty:seq.word
 else
  " &br the word" + w.p + "occurs" + toword.count.p + "times."

function removelowcount(mincount:int, p:wordfreq)seq.wordfreq if count.p < mincount then empty:seq.wordfreq else [ p]

function wordfreq(mincount:int, a:seq.seq.word)seq.wordfreq
 ((for(@e ∈ sort.(for(@e ∈ a, acc = sparseseq.wordfreq(0,"A"_1))count(acc, @e)), acc = empty:seq.wordfreq)acc + removelowcount(mincount, @e)))
 
Function testwordfreq(count:int,text:seq.seq.word) seq.word
 ((for(@e ∈ wordfreq(count, text), acc = empty:seq.word)acc + print.@e))

Function testwordfreq seq.word((for(@e ∈ wordfreq(300, gettext."stdlib/pass2.ls"), acc = empty:seq.word)acc + print.@e))

function count(s:seq.wordfreq, w:seq.word)seq.wordfreq(for(@e ∈ w, acc = s)count(acc, @e))