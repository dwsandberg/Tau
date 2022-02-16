Module compilerfrontT.T

use compilerfront

use standard

use symbol

use typedict

use process.compileinfo

use set.symdef

use seq.seq.word

unbound depententinfo:T(s:seq.word)loadedresult

unbound pass2:T(set.symdef, typedict)set.symdef

Function compileinfo:T(option:seq.word, info:seq.seq.word)process.compileinfo
{OPTION INLINE}
let a = break(first.info, "uses exports", true)
let dependentlibs = depententinfo:T(a_2 << 1)
YYYY:T(option, info, dependentlibs)

Function compilerfront4:T(option:seq.word, allsrc:seq.seq.word, libinfo:loadedresult)compileinfo
let a = compilerfront3(option, allsrc, libinfo)
finish(a
, if first.option.a ∈ "library text hhh pass1"then prg.a
else pass2:T(prg.a, typedict.a) ∪ templates.a
)

function YYYY:T(option:seq.word, info:seq.seq.word, dependentlibs:loadedresult)process.compileinfo
{OPTION NOINLINE}
{need because wasm interpreted code does not handle createthreadY}
process.compilerfront4:T(option, info, dependentlibs) 