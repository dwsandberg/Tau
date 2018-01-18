module libdesc

use etype

use groupparagraphs

use libscope

use parse

use seq.libdesc

use seq.moddesc

use seq.mytype

use seq.seq.seq.word

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
  moddesc(name_1, libname, a, @(+, finduseclause, empty:seq.mytype, a), not(name_1 in exports))

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
  let l = libdesc(libname, uses, src, exports)
  l

Function =(a:moddesc, b:moddesc)boolean modname.a = modname.b

Function ?(a:moddesc, b:moddesc)ordering modname.a ? modname.b

Function findlibclause(a:seq.seq.word, i:int)seq.word 
 assert i < length.a report"No Library clause found"
  let s = a_i 
  if s_1 ="Library"_1 then s else findlibclause(a, i + 1)

function gettext2(libname:word, e:seq.word, a:word)seq.moddesc 
 @(+, moddesc(libname, e), empty:seq.moddesc, groupparagraphs("module Module", gettext.[ merge([ libname]+"/"+ a +".ls")]))

Function parseUse(a:seq.word)mytype mytype(parse(a, tree("X"_1))_1)

function mytypeb(t:tree.word)seq.word 
 if nosons.t = 0 then [ label.t]else mytypeb(t_1)+ [ label.t]

Function mytype(t:tree.word)mytype mytype.mytypeb.t

