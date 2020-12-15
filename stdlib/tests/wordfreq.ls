#!/usr/local/bin/tau ; use test2 ; test2

Module wordfreq

Count word frequence in text file. An indexed encoding is used to assign indexes to each distinct word in the file. Uses a dseq to provide a 0 count for words that have not yet been encountered and assigned an index. 

use fileio

use encoding.indexedword

use standard

use textio

use seq.seq.word


use otherseq.wordfreq

use seq.wordfreq

use sparseseq.wordfreq

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
 sort(a @ count(sparseseq.wordfreq(0,"A"_1), @e))
 @ +(empty:seq.wordfreq, removelowcount(mincount, @e))

Function testwordfreq seq.word wordfreq(300, gettext."stdlib/pass2new.ls") @ +(empty:seq.word, print.@e)

function count(s:seq.wordfreq, w:seq.word)seq.wordfreq w @ count(s, @e)