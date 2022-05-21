Module compilerfrontT.T

use compilerfront

use standard

use symbol

use typedict

use otherseq.mytype

use seq.symbol

use set.symdef

use seq.seq.word

unbound pass2:T(set.symdef, typedict, option:seq.word)set.symdef

Function compilerfront2:T(option:seq.word, allsrc:seq.seq.word, libinfo:midpoint)midpoint
{OPTION PROFILE}
let m = compilerfront3(option, allsrc, libinfo)
if first.option.m ∈ "library text hhh pass1"then m
else
 let prg5 = pass2:T(prg.m, typedict.m, "") ∪ templates.m
 if option = "all2"then prepareback(prg5, m, libinfo)
 else midpoint(option, prg5, typedict.m, libmods.m, src.m) 