Module sid

use core

use libdesc

use main

Function asword(a:session)word export

Function =(a:session, b:session)boolean export

Function hash(a:session)int export

Function user(session)seq.word export

Function newsession(s:session)session export

Function icmd(name:seq.word, funcname:seq.word, class:word, arg:seq.word)icmd export

Function icmd(a:seq.word)icmd export

Function cmdresult(sid:session, cmds:seq.icmd, text:seq.word)cmdresult export

Function cmdresult(sid:session, cmds:seq.icmd, text:seq.word, pos:seq.word)cmdresult export

Function compilelib(word)seq.word export

Function execute(s:session, funcname:word, modname:word, libname:word)cmdresult export

Function writemodule(s:session, libname:word, modname:word, newtext:seq.seq.word)seq.word export

Function readmodule(s:session, libname:word, modname:word)seq.seq.word export

Function uses(moddesc)seq.mytype export

Function libname(moddesc)word export

Function modname(a:moddesc)word export

Function modules(l:libdesc)seq.moddesc export

Function allmodules(l:libdesc)seq.moddesc export

Function find(modname:word, l:seq.moddesc)seq.moddesc export

Function tolibdesc(libname:word)libdesc export

Function moddesc(libname:word, exports:seq.word, a:seq.seq.word)moddesc export

Function =(a:moddesc, b:moddesc)boolean export

Function ?(a:moddesc, b:moddesc)ordering export

