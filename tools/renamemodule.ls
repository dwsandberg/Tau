Module renamemodule

use seq.mapnames

use seq.seq.word

use seq.word

use stdlib

function mapentry(n:seq.word, i:int)int 
 let x = encode(mapnames(n_i, n_(i + 1)), encodenames)
  0

Function setmap(namelist:seq.word)seq.word 
 let discard = @(+, mapentry.namelist, 0, arithseq(length.namelist / 2, 2, 1))
  {"OK"}

type mapnames is record old:word, new:word

function =(a:mapnames, b:mapnames)boolean old.a = old.b

function hash(a:mapnames)int hash.old.a

type encodenames is encoding mapnames

Function mapname(n:word)word new.decode(encode(mapnames(n, n), encodenames), encodenames)

