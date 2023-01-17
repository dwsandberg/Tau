Module tools

use file

use standard

use prettycompilerfront

use frontcmd

use llvmcode

use compilerfrontT.callconfig

use symbol2

Function front(input:seq.file, o:seq.word, pass:seq.word, n:seq.word, ~n:seq.word
 , mods:seq.word, ~mods:seq.word, within:boolean, out:seq.word) seq.file
let cf = compilerFront:callconfig(if isempty.pass then "pass2" else pass, input),
front(cf, o, pass, n, ~n, mods, ~mods, within, out)

Function unusedsymbols(input:seq.file
 , o:seq.word
 , flags:seq.word
 , all:boolean
 , generated:boolean
 , excessExports:boolean) seq.file
unusedsymbols(compilerFront:callconfig("text", input), o, flags, all, generated, excessExports)

Function transform(input:seq.file
 , o:seq.word
 , target:seq.word
 , modrename:seq.word
 , parseit:boolean
 , reorguse:boolean
 , html:boolean
 , noindex:boolean
 , cleanexports:boolean
 , moveexports:boolean) seq.file
let m = 
 if parseit ∨ cleanexports ∨ moveexports then
  compilerFront:callconfig("text", input)
 else
  empty:midpoint
,
transform(m, o, target, modrename, parseit
 , reorguse, html, noindex, cleanexports, moveexports
 , input) 