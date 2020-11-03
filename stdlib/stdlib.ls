#!/usr/local/bin/tau

Module stdlib 

Library stdlib UTF8 bitpackedseq bits blockseq codetemplates   encoding fileio 
format graph groupparagraphs  internalbc ipair libdesc  llvm main2  otherseq   
parse pass1   persistant  prims process real   seq set stack stacktrace symbol textio tree worddict xxhash 
 timestamp maindict words   newpretty  codegennew pass2new intdict  
 mangle mytype
parsersupport postbind uses 
 exports stdlib main2 maindict UTF8    words   assignencodingnumber
  bits blockseq   encoding fileio format  llvmconstants llvm
  ipair       process real   seq set stack stacktrace 
  textio  prims      otherseq tree graph   
  newpretty 
  worddict groupparagraphs 
 timestamp ioseq dataio intdict dict
    parsersupport mangle mytype   bitpackedseq xxhash
        libdesc
   pass2new   symbol internalbc parse
  
 
 
  PROFILE      pass1:pass1(seq.seq.seq.word,seq.word ,seq.liblib ) linkage

 
  PROFILE      pass1:postbind( seq.myinternaltype, set.symbol, set.symbol
, seq.symbol,int, program, program, program) program
 
  PROFILE      pass1:postbind3( seq.myinternaltype, set.symbol, seq.symbol,
int, seq.symbol, mytype, seq.word, set.symbol, program, program)resultpb

 
  *  PROFILE  main2:compilelib2(word) seq.word  

 *  PROFILE main2:subcompilelib(word) seq.word 

 / *  PROFILE   pass2new: pass2(   program,set.symbol
 ,seq.symbol,seq.firstpass,program,seq.word) intercode
 
  /*  PROFILE   pass2new:depthfirst(program, int, seq.symbol, program, seq.symbol, symbol) program
     
/ *   PROFILE pass2new:firstopt( program,  symbol,  seq.symbol) program
  
 /   *   PROFILE pass2new:yyy( program, seq.symbol,  int, seq.symbol, int,  worddict.seq.symbol)
  
 / *  NOINLINE symbol: isconst( symbol)boolean
  
 / *  NOINLINE symbol: isspecial( symbol)boolean
  
 / * INLINE pass2new :inline( program, seq.symbol, int, seq.symbol,   int, int, seq.symbol,worddict.seq.symbol)
 expandresult
 
  / * INLINE pass2new : applycode( program ,seq.symbol, int, seq.symbol,  int,    worddict.seq.symbol)  expandresult

 
  * NOINLINE  seq.symbol:packed(seq.symbol) seq.symbol
     


/* PROFILE codegennew:codegen(program,  seq.symbol,  set.symbol,  word, symbol)seq.bits

/* PROFILE  codetemplates:match5map(  program,  seq.symbol,  set.symbol, seq.word) seq.match5
 
/* PROFILE  codetemplates:  buildtemplates(  seq.symbol, int, program, seq.symbol) seq.match5 

/* PROFILE codetemplates: processconst(   seq.symbol, int,  seq.symbol) seq.match5


* STATE builtin: addencoding(  seq.T, encodingrep.T, int ) int  

* STATE builtin: addencoding(  int, seq.T, int ) int  

* STATE builtin: getinstance( seq.T) ptr

* STATE builtin: getfile(seq.bits ) fileresult 

* STATE builtin: setfld(seq.T , int, seq.T)  int

* STATE  builtin: option(T,seq.word )T  




use UTF8

use seq.int

use seq.seq.int

use seq.seq.word

use seq.word

use xxhash

use otherseq.int

use otherseq.word

use words




type ordering is record toint:int

type boolean is record toint:int

* Useful constants

Function openpara word {"("_1 }

Function closepara word {")"_1 }

Function comma word {","_1 }

Function openbracket word {"["_1 }

Function closebracket word {"]"_1 }

Function colon word {":"_1 }

Function space word encodeword.[ char.32]



* EQ GT and LT are the possible results of ? operator

Function EQ ordering ordering.1

Function GT ordering ordering.2

Function LT ordering ordering.0

Function true boolean boolean.1

Function false boolean boolean.0

-----------------

Function toint(boolean)int export


Function-(i:int)int 0 - i

Function ?(a:int, b:int)ordering builtin.usemangle

/Function process2(a:int) int builtin.usemangle

Function ?(a:ordering, b:ordering)ordering toint.a ? toint.b

Function +(a:int, b:int)int builtin.usemangle

Function-(a:int, b:int)int builtin.usemangle

Function *(a:int, b:int)int builtin.usemangle

Function /(a:int, b:int)int builtin.usemangle

Function hash(i:int)int finalmix.hash(hashstart, i)

Function =(a:int, b:int)boolean builtin.usemangle

Function =(a:ordering, b:ordering)boolean toint.a = toint.b

Function =(a:boolean, b:boolean)boolean toint.a = toint.b

Function toword(o:ordering)word {"LT EQ GT"_(toint.o + 1)}

Function ∧(a:ordering, b:ordering)ordering 
 let x = a 
  if x = EQ then b else x

--------------------

Function ?(a:boolean, b:boolean)ordering toint.a ? toint.b

Function ∧(a:boolean, b:boolean)boolean 
 if a then b else // false // boolean.0

Function ∨(a:boolean, b:boolean)boolean 
 if a 
  then // true is not use so simple inline expansion is used to produce short circuit evaluation // 
   boolean.1 
  else b

Function not(a:boolean)boolean builtin.usemangle

Function abs(x:int)int if x < 0 then 0 - x else x

Function mod(x:int, y:int)int if x < 0 then x - x / y * y + y else x - x / y * y

Function >(a:int, b:int)boolean builtin.usemangle

Function <(a:int, b:int)boolean export

Function ≤(a:int, b:int)boolean export

Function ≥(a:int, b:int)boolean export

Function max(a:int, b:int)int if a > b then a else b

Function min(a:int, b:int)int if a < b then a else b

Function between(i:int, lower:int, upper:int)boolean i ≥ lower ∧ i ≤ upper

---------------------------



Function hash(a:seq.int)int finalmix.@(hash, identity, hashstart, a)



Function hash(a:seq.word)int finalmix.@(hash, hash, hashstart, a)




Function^(i:int, n:int)int @(*, identity, 1, constantseq(n, i))

Function pseudorandom(seed:int)int 
 let ah = 16807 
  let mh = 2147483647 
  let test = ah *(seed mod(mh / ah)) - mh mod ah *(seed /(mh / ah))
  if test > 0 then test else test + mh

function addrandom(s:seq.int, i:int)seq.int s + pseudorandom(s_length.s)

Function randomseq(seed:int, length:int)seq.int @(addrandom, identity, [ seed], constantseq(length - 1, 1))

Function randomint(i:int)seq.int builtin.usemangle

/Function lines(a:seq.word, b:seq.word)seq.word a + EOL + b

Function seperator(sep:seq.word, s:seq.word, w:seq.word)seq.word 
 if length.s = 0 then w else s + sep + w

Function seperator(sep:seq.word, s:seq.word, w:word)seq.word 
 // Good for adding commas in seq of words. @(seperator(",", toword,"", [ 1, 2, 3])// 
  if length.s = 0 then [ w]else s + sep + w
  

Function hash(a:word)int export

Function ?(a:word, b:word)ordering export

Function =(a:word, b:word)boolean export

Function ≠(a:word, b:word)boolean export

Function ≠(a:int, b:int)boolean export
 
Function toword(n:int)word 
 // Covert integer to  a single word. // 
 export
 
Function toint(w:word)int 
 // Convert an integer represented as a word to an int // export
 
Function merge(a:seq.word)word 
 // make multiple words into a single word. // export

Function type:ordering internaltype  export

Function type:boolean internaltype  export

Function type:word  internaltype  export

Function type:seq.word  internaltype  export

Function type:seq.seq.word  internaltype  export

Function type:seq.int internaltype export


Function empty:seq.seq.word seq.seq.word  export

Function empty:seq.word  seq.word export

Function empty:seq.int  seq.int export

Function arithseq(int, int, int)seq.int export

Function constantseq(len:int, element:int)seq.int export

Function_(seq.word, int)word export

Function_(seq.seq.word, int)seq.word export

Function_(seq.int, int)int export

Function_(s:pseq.seq.word, i:int)seq.word export

Function_(pseq.int, int)int export

Function_(a:pseq.word, b:int)word export

Function length(seq.word)int export

Function length(seq.seq.word)int export

Function length(seq.int)int export

Function findindex(word, seq.word)int export

/Function findindex(seq.word, seq.seq.word)int export

Function findindex(word, seq.word, int)int export

Function identity(seq.word)seq.word export

Function identity(word)word export

Function identity(int)int export

Function last(s:seq.word)word export

Function subseq(seq.seq.word, int, int)seq.seq.word export

Function subseq(seq.word, int, int)seq.word export

Function subseq(seq.int, int, int)seq.int export

Function in(word, seq.word)boolean export

Function in(seq.word, seq.seq.word)boolean export

Function in(int, seq.int)boolean export

Function =(seq.word, seq.word)boolean export

Function =(seq.int, seq.int)boolean export

Function +(seq.word, word)seq.word export

Function +(seq.int, seq.int)seq.int export

Function +(seq.int, int)seq.int export

Function last(seq.int) int export

Function +(seq.seq.word, seq.word)seq.seq.word export

Function +(seq.seq.word, seq.seq.word)seq.seq.word export

Function +(a:seq.word, b:seq.word)seq.word export

Function nbspchar char export


Function alphasort(a:seq.word)seq.word export 


Function alphasort(a:seq.seq.word)seq.seq.word export

type char is record toint:int

Function =(a:char,b:char) boolean toint.a=toint.b

Function ?(a:char,b:char) ordering toint.a ? toint.b

Function hash(a:char) int hash.toint.a


Function type:char internaltype  export

Function type:seq.char internaltype  export

Function length(seq.char) int export

Function empty:seq.char seq.char export

Function +(seq.char, seq.char) seq.char export

Function isempty(seq.char) boolean export

Function _(seq.char, int) char export

Function _(pseq.char, int) char export

Function subseq(seq.char, int, int) seq.char export

Function =(seq.char, seq.char) boolean export

Function +(seq.char, char) seq.char export


Function toint(char) int export

Function char(int) char export

Function  char1(s:seq.word) char  (decodeword.(s_1))_1 

Function encodeword(a:seq.char)word  export

Function decodeword(w:word)seq.char export

Function print( decimals:int,rin:real) seq.word export

Function checkinteger(w:word)word export



use seq.char

  
* usegraph include  xxhash encoding   bits  words real subreal
stacktrace  textio reconstruct  UTF8  seq otherseq fileio
blockseq  stdlib exclude stdlib seq  




* usegraph include  prims   tree  graph ipair libscope internalbc
process stack set   format groupparagraphs    bitpackedseq maindict worddict
exclude stdlib seq 

* usegraph include  main2 libscope display constant codegen convert 
 parse pass1  symbol libdesc
codetemplates pass2 persistant   llvm  postbind
reconstruct persistantseq opt2
symbol parse libdesc internalbc intercode cvttoinst codegen pass2new codegennew funcsig
exclude seq set otherseq stdlib bits tree graph UTF8 stack stacktrace real process  ipair 
bitpackedseq   fileio blockseq textio encoding words 
   


