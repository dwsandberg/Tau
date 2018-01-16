Module test2

type wordfreq is record count:int, w:word

use fileresult

use oseq.wordfreq

use seq.seq.word

use seq.word

use seq.wordfreq

use stdlib

function =(a:wordfreq, b:wordfreq)boolean false

function ?(a:wordfreq, b:wordfreq)ordering count.a ? count.b

function count(s:seq.wordfreq, w:word)seq.wordfreq 
 replace(s, encoding.w, wordfreq(count(s_encoding.w)+ 1, w))

function print(p:wordfreq)seq.word 
 if count.p = 0 
  then empty:seq.word 
  else"&br the word"+ w.p +"occurs"+ toword.count.p +"times."+ EOL

function removelowcount(mincount:int, p:wordfreq)seq.wordfreq 
 if count.p < mincount then empty:seq.wordfreq else [ p]

function wordfreq(mincount:int, a:seq.seq.word)seq.wordfreq 
 sort.@(+, removelowcount.mincount, empty:seq.wordfreq, @(count, identity, dseq.wordfreq(0,"A"_1), a))

Function test2 seq.word @(+, print, empty:seq.word, wordfreq(300, gettext."testall/input"))

function count(s:seq.wordfreq, w:seq.word)seq.wordfreq @(count, identity, s, w)

