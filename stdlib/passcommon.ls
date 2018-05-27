Module passcommon

use libscope

use processtypes

use seq.func

use seq.libtype

use seq.mod2desc

use set.word

use stdlib

use symbol

Function mytype(seq.word)mytype export

Function assigntypesizes(seq.libtype)set.libtype export

Function print(libtype)seq.word export

Function sizeoftype(set.libtype, mytype)offset export

Function fldsoftype(set.libtype, mytype)seq.mytype export

Function libtypes(set.libtype, libsym)set.libtype export

Function ?(a:libtype, b:libtype)ordering export


Function libtypes(seq.word, set.libtype, mytype)set.libtype export

Function lookuptypes(seq.word, set.libtype, syminfo)set.libtype export

Function deepcopytypes2(set.libtype, mytype)seq.mytype export

Function +(mytype, word)mytype export

Function print(syminfo)seq.word export

Function actualreturntype(syminfo)mytype export

Function funcfrominstruction(set.libtype, seq.word, mytype, int)seq.word export

Function paralistcode(int)seq.word export

Function replaceTsyminfo(mytype, syminfo)syminfo export

Function CALLcode(syminfo)seq.word export

Function FREFcode(syminfo)seq.word export

Function finddeepcopyfunction(mytype)syminfo export

Function codingrecord(syminfo)seq.word export

Function calls(syminfo)set.word export

Function compileinstance(set.libtype, set.syminfo, word)seq.syminfo export

type mod2desc is record modname:mytype, export:set.syminfo, uses:seq.mytype, typedefs:seq.libtype, defines:set.syminfo, tocompile:seq.seq.word, isprivate:boolean

Function typedefs(mod2desc)seq.libtype export

Function modname(m:mod2desc)mytype export

Function tocompile(mod2desc)seq.seq.word export

Function export(s:mod2desc)set.syminfo export

Function defines(s:mod2desc)set.syminfo export

Function uses(s:mod2desc)seq.mytype export

Function isprivate(a:mod2desc)boolean export

Function mod2desc(modname:mytype, export:set.syminfo, uses:seq.mytype, typedefs:seq.libtype, defines:set.syminfo, tocompile:seq.seq.word, isprivate:boolean)mod2desc 
 export

type pass1result is record code:intercode2, libname:seq.word, newcode:seq.syminfo, compiled:seq.syminfo, 
mods:seq.mod2desc, existingtypes:set.libtype, alltypes:set.libtype

Function pass1result(code:intercode2, libname:seq.word, newcode:seq.syminfo, compiled:seq.syminfo, mods:seq.mod2desc, existingtypes:set.libtype, alltypes:set.libtype)pass1result 
 export


Function pass1result(libname:seq.word, newcode:seq.syminfo, compiled:seq.syminfo, mods:seq.mod2desc, existingtypes:set.libtype, alltypes:set.libtype)pass1result 
 pass1result(emptyintercode, libname, newcode, compiled, mods, existingtypes, alltypes)

Function code(pass1result) intercode2 export

Function libname(pass1result)seq.word export

Function newcode(pass1result)seq.syminfo export

Function compiled(pass1result)seq.syminfo export

Function mods(pass1result)seq.mod2desc export

Function existingtypes(pass1result)set.libtype export

Function alltypes(pass1result)set.libtype export

function setprivate(exports:seq.word, m:mod2desc)mod2desc 
 // let b = not(abstracttype.modname.m in exports)assert b = isprivate.m report"???"+ towords.modname.m // 
  mod2desc(modname.m, export.m, uses.m, typedefs.m, defines.m, tocompile.m, not(abstracttype.modname.m in exports))

Function setprivate(exports:seq.word, a:pass1result)pass1result 
 pass1result(code.a, libname.a, newcode.a, compiled.a, @(+, setprivate.exports, empty:seq.mod2desc, mods.a), existingtypes.a, alltypes.a)

Function ?(a:syminfo, b:syminfo)ordering export

use parse

use pretty



Function parse(seq.word,tree.word) tree.word export

Function prettyparagraph(control:prettycontrol, p:seq.word)seq.word export

Function prettytree(control:prettycontrol, t:tree.word)seq.word export

Function print(t:tree.word)seq.word export


Function parsefuncheader(text:seq.word)tree.word export


Function expression(s:seq.word)tree.word export

type  inst is record towords:seq.word,flags:seq.word,returntype:mytype

Function inst(towords:seq.word,flags:seq.word,returntype:mytype) inst export

Function mangledname(a:inst)  word  { (towords.a)_1 }

Function nopara(a:inst)  int  toint((towords.a)_2)

function flags(a:inst) seq.word export

function towords(a:inst) seq.word export


function returntype(a:inst) mytype export


type intercode2 is record codes:seq.seq.int, coding:seq.inst ,defines:seq.int

Function emptyintercode intercode2 intercode2(empty:seq.seq.int, empty:seq.inst ,empty:seq.int)

defines are indices into coding that indicate which functions are defined and indices into codes that give a seq of integers which are indices into coding 

function intercode2(seq.seq.int, seq.inst, seq.int) intercode2 export

function codes(intercode2) seq.seq.int export

function coding(intercode2) seq.inst export

function defines(intercode2) seq.int export

use seq.seq.int

use seq.int

use seq.inst
