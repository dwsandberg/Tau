Module passcommon




use libscope


use processtypes

use seq.func

use seq.libtype

use seq.mod2desc

use set.word

use stdlib

use symbol


Function mytype(seq.word) mytype export

Function assigntypesizes(seq.libtype)set.libtype export

Function print(libtype)seq.word export

Function sizeoftype(set.libtype, mytype)offset export

Function fldsoftype(set.libtype, mytype)seq.mytype export

Function libtypes(set.libtype, libsym)set.libtype export

Function libtypes(seq.word, set.libtype, mytype)set.libtype export

Function lookuptypes(seq.word, set.libtype, syminfo)set.libtype export

Function deepcopytypes2(set.libtype, mytype)seq.mytype export

Function +(mytype, word)mytype export

Function print(syminfo)seq.word export

Function actualreturntype(syminfo)mytype export

/Function parsesyminfo(mytype, seq.word)syminfo export

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

type pass1result is record code:seq.func, libname:seq.word, newcode:seq.syminfo, compiled:seq.syminfo, mods:seq.mod2desc, existingtypes:set.libtype, alltypes:set.libtype

Function pass1result(code:seq.func, libname:seq.word, newcode:seq.syminfo, compiled:seq.syminfo, mods:seq.mod2desc, existingtypes:set.libtype, alltypes:set.libtype)pass1result 
 export

Function pass1result(libname:seq.word, newcode:seq.syminfo, compiled:seq.syminfo, mods:seq.mod2desc, existingtypes:set.libtype, alltypes:set.libtype)pass1result 
 pass1result(empty:seq.func, libname, newcode, compiled, mods, existingtypes, alltypes)

Function code(pass1result)seq.func export

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

