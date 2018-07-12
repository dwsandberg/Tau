module libdesc

use groupparagraphs

use libscope

use oseq.word

use parse

use seq.libdesc

use seq.moddesc

use seq.mytype

use seq.seq.seq.word

use seq.seq.word

use seq.word

use seq.tree.word

use stdlib

use textio

use tree.word

type libdesc is record name:word, dependentlibs:seq.word, modules:seq.moddesc, exports:seq.word

type moddesc is record modname:word, libname:word, src:seq.seq.word, uses:seq.mytype, private:boolean

Function uses(moddesc)seq.mytype export

Function libname(moddesc)word export

Function name(libdesc)word export

Function modname(a:moddesc)word export

Function src(moddesc)seq.seq.word export

Function modules(l:libdesc)seq.moddesc export

Function dependentlibs(libdesc)seq.word export

Function exports(libdesc)seq.word export

Function libdesc(name:word, dependentlibs:seq.word, modules:seq.moddesc, exports:seq.word)libdesc 
 export

Function moddesc(libname:word, exports:seq.word, a:seq.seq.word)moddesc 
 let name = if length.a = 0 then""else subseq(a_1, 2, 2)
  let rs2 = prepreplacements("","","le ≤ ge ≥ ne ≠ and ∧ or ∨ cup ∪ cap ∩ in ∈ contains ∋", 1)
  let b = @(+, replacements(subseq(rs2, 1, length.rs2 / 2), subseq(rs2, length.rs2 / 2 + 1, length.rs2)), empty:seq.seq.word, a)
  moddesc(name_1, libname, b, @(+, finduseclause, empty:seq.mytype, b), not(name_1 in exports))

function replacements(a:seq.word, b:seq.word, t:seq.word)seq.word @(+, replace(a, b),"", t)

function replace(a:seq.word, b:seq.word, c:word)word 
 let i = binarysearch(a, c)
  if i > 0 then b_i else c

function prepreplacements(old:seq.word, new:seq.word, pairs:seq.word, i:int)seq.word 
 // the pair elements in pair are one after the other. The first element will be merged with a"&".The result is the first elements sorted followed by the second elements rearranged to match the sort. // 
  if i > length.pairs 
  then old + new 
  else let val = merge("&"+ pairs_i)
  let j = binarysearch(old, val)
  prepreplacements(subseq(old, 1,-j - 1)+ [ val]+ subseq(old,-j, length.old), subseq(new, 1,-j - 1)+ [ pairs_(i + 1)]+ subseq(new,-j, length.new), pairs, i + 2)

function finduseclause(s:seq.word)seq.mytype 
 if subseq(s, 1, 1)="use"then [ parseUse.s]else empty:seq.mytype

Function allmodules(l:libdesc)seq.moddesc 
 @(+, modules, empty:seq.moddesc, @(+, tolibdesc, [ l], dependentlibs.l))

Function find(modname:word, l:seq.moddesc)seq.moddesc 
 findelement(moddesc(modname, modname, ["module"+ modname], empty:seq.mytype, false), l)

Function tolibdesc(libname:word)libdesc 
 let a = gettext.[ merge([ libname]+"/"+ libname +".ls")]
  let s = findlibclause(a, 1)
  let u = findindex("uses"_1, s, 3)
  let e = findindex("exports"_1, s, 3)
  let uses = subseq(s, u + 1, e - 1)
  let filelist = subseq(s, 2, min(u - 1, e - 1))
  let exports = subseq(s, e + 1, length.s)
  let src = @(+, gettext2(s_2, exports), empty:seq.moddesc, filelist)
  libdesc(libname, uses, src, exports)

Function =(a:moddesc, b:moddesc)boolean modname.a = modname.b

Function ?(a:moddesc, b:moddesc)ordering modname.a ? modname.b

Function findlibclause(a:seq.seq.word, i:int)seq.word 
 assert i < length.a report"No Library clause found"
  let s = a_i 
  if s_1 ="Library"_1 then s else findlibclause(a, i + 1)

Function findlibclause2(a:seq.seq.word, i:int)seq.word 
 assert i < length.a report"No Library clause found"
  let s = a_i 
  if s_1 ="Library"_1 then s else findlibclause2(a, i + 1)

function gettext2(libname:word, e:seq.word, a:word)seq.moddesc 
 @(+, moddesc(libname, e), empty:seq.moddesc, groupparagraphs("module Module", gettext.[ merge([ libname]+"/"+ a +".ls")]))

Function parseUse(a:seq.word)mytype mytype(parse(a, tree("X"_1))_1)

function mytypeb(t:tree.word)seq.word 
 if nosons.t = 0 then [ label.t]else mytypeb(t_1)+ [ label.t]

Function mytype(t:tree.word)mytype mytype.mytypeb.t

