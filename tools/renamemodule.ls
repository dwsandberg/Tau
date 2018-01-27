Module renamemodule

use libdesc

use libscope

use seq.mapnames

use seq.moddesc

use stdlib

function mapentry(n:seq.word, i:int)int 
 let x = encode(mapnames(n_i, n_(i + 1)), encodenames)
  0

Function maplib(a:libdesc, namelist:seq.word)libdesc 
 let discard = @(+, mapentry.namelist, 0, arithseq(length.namelist / 2, 2, 1))
  libdesc(name.a, dependentlibs.a, @(+, mapmod, empty:seq.moddesc, modules.a), @(+, mapname,"", exports.a))

function mapmod(m:moddesc)moddesc 
 moddesc(libname.m, empty:seq.word, @(+, mapp, empty:seq.seq.word, src.m))

function mapp(a:seq.word)seq.word 
 if a_1 in"use Module module"then [ a_1]+ mapname(a_2)+ subseq(a, 3, length.a)else a

type mapnames is record old:word, new:word

function =(a:mapnames, b:mapnames)boolean old.a = old.b

function hash(a:mapnames)int hash.old.a

type encodenames is encoding mapnames

function mapname(n:word)word new.decode(encode(mapnames(n, n), encodenames), encodenames)

