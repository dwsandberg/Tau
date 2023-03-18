Module tools

use file

use standard

use frontcmd.callconfig

use llvmcode

use compilerfrontT.callconfig

use symbol2

Export compilerFront:callconfig (seq.word, seq.file) midpoint


/Export 
  front:callconfig(input:seq.file, o:seq.word, pass:seq.word, n:seq.word, ~n:seq.word
 , mods:seq.word, ~mods:seq.word, within:boolean, out:seq.word) seq.file


/Export unusedsymbols:callconfig(input:seq.file
 , o:seq.word
 , flags:seq.word
 , all:boolean
 , generated:boolean
 , excessExports:boolean) seq.file
 

/Export transform:callconfig(input:seq.file
 , o:seq.word
 , target:seq.word
 , modrename:seq.word
 , parseit:boolean
 , reorguse:boolean
 , html:boolean
 , noindex:boolean
 , cleanexports:boolean
 , moveexports:boolean) seq.file

