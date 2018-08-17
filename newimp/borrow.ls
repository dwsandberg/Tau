Module borrow

* usegraph include newimp pass2 newparse other libdescfunc borrow borrow2 cvttoinst Symbol codegen altgen main exclude real seq set graph stack stdlib bits tree ipair stacktrace

use libscope

function mytype(seq.word)mytype export

function towords(mytype)seq.word export

function =(mytype, mytype)boolean export

function mangle(word, mytype, seq.mytype)word export

function replaceT(mytype, mytype)mytype export

function print(mytype)seq.word export

function abstracttype(mytype)word export

function parameter(mytype)mytype export

function iscomplex(mytype)boolean export

function codedown(word)seq.seq.word export

Function libname(liblib)seq.word export

Function mods(liblib)seq.libmod export

Function types(liblib)seq.libtype export

Function returntype(libsym)seq.word export

Function instruction(libsym)seq.word export

Function fsig(libsym)word export

Function library(libmod)word export

Function parameterized(libmod)boolean export

Function modname(libmod)word export

Function defines(libmod)seq.libsym export

Function exports(libmod)seq.libsym export

Function libmod(parameterized:boolean, modname:word, defines:seq.libsym, exports:seq.libsym, library:word)libmod 
 export

Function liblib(a:seq.word, c:seq.libtype, d:seq.libmod)liblib export

Function libsym(returntype:mytype, manglename:word, inst:seq.word)libsym export

Function isabstract(a:mytype)boolean export

Function print(l:libsym)seq.word export

Function emptyliblib(libname:word)liblib export

