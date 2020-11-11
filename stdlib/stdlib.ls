Module stdlib 

Library stdlib UTF8 bitpackedseq bits  codetemplates   encoding fileio 
format graph groupparagraphs  internalbc ipair libdesc  llvm main2  otherseq   
parse pass1   persistant  prims process real   seq set stack stacktrace symbol textio tree worddict xxhash 
 timestamp maindict words   newpretty  codegennew pass2new intdict  
 mangle mytype llvmconstants
parsersupport postbind uses 
 exports stdlib main2 maindict UTF8    words   assignencodingnumber
  bits   encoding fileio format  llvmconstants llvm
  ipair       process real   seq set stack stacktrace 
  textio  prims      otherseq tree graph   
  newpretty 
  worddict groupparagraphs 
 timestamp ioseq dataio intdict dict
    parsersupport mangle mytype   bitpackedseq xxhash
      symbol internalbc     parse   libdesc
 
 
  PROFILE      pass1:pass1(seq.seq.seq.word,seq.word ,seq.liblib ) linkage

 
  PROFILE      pass1:postbind( typedict, set.symbol, set.symbol
, seq.symbol,int, program, program, program) program
 
  PROFILE      pass1:postbind3( typedict, set.symbol, seq.symbol,
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

 
  * INLINE   symbol:Lit(int)  symbol
     
  * NOINLINE  UTF8:toword(int) word 

/* PROFILE codegennew:codegen(program,  seq.symbol,  set.symbol,  word, symbol)seq.bits

/* PROFILE  codetemplates:match5map(  program,  seq.symbol,  set.symbol, seq.word) seq.match5
 
/* PROFILE  codetemplates:  buildtemplates(  seq.symbol, int, program, seq.symbol) seq.match5 

/* PROFILE codetemplates: processconst(   seq.symbol, int,  seq.symbol) seq.match5


* STATE builtin: addencoding(  seq.T, encodingrep.T, int ) int  

* STATE builtin: addencoding(  int, seq.T, int ) int  

* STATE builtin: getinstance( seq.T) ptr

* STATE builtin: getfile(seq.bits ) fileresult 

* STATE builtin: setfld(seq.int , int, seq.T)  int

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

 Builtin ?(a:int, b:int)ordering  


Function ?(a:ordering, b:ordering)ordering toint.a ? toint.b

 Builtin +(a:int, b:int)int  

 Builtin -(a:int, b:int)int  

 Builtin *(a:int, b:int)int  

 Builtin /(a:int, b:int)int  

Function hash(i:int)int finalmix.hash(hashstart, i)

 Builtin =(a:int, b:int)boolean  

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

 Builtin not(a:boolean)boolean  

Function abs(x:int)int if x < 0 then 0 - x else x

Function mod(x:int, y:int)int if x < 0 then x - x / y * y + y else x - x / y * y

 Builtin >(a:int, b:int)boolean  

Export <(a:int, b:int)boolean  

Export ≤(a:int, b:int)boolean  

Export  ≥(a:int, b:int)boolean  

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

 Builtin randomint(i:int)seq.int  

 
Function seperator(sep:seq.word, s:seq.word, w:seq.word)seq.word 
 if length.s = 0 then w else s + sep + w

Function seperator(sep:seq.word, s:seq.word, w:word)seq.word 
 // Good for adding commas in seq of words. @(seperator(",", toword,"", [ 1, 2, 3])// 
  if length.s = 0 then [ w]else s + sep + w
  

Export hash(a:word)int 

Export ?(a:word, b:word)ordering 

Export =(a:word, b:word)boolean 

Export ≠(a:word, b:word)boolean 

Export ≠(a:int, b:int)boolean 
 
Export toword(n:int)word 
 // Covert integer to  a single word. // 
 
 
Export toint(w:word)int 
 // Convert an integer represented as a word to an int // 
 
Export merge(a:seq.word)word 
 // make multiple words into a single word. // 

Export type:ordering  

Export type:boolean  

Export type:word   

Export type:seq.word   

Export type:seq.seq.word     

Export type:seq.int  

Export type:seq.char    

Export type:encoding.seq.char    

use encoding.seq.char

Export empty:seq.seq.word seq.seq.word  

Export empty:seq.word  seq.word 

Export empty:seq.int  seq.int 

Export arithseq(int, int, int)seq.int 

Export constantseq(len:int, element:int)seq.int 

Export _(seq.word, int)word 

Export _(seq.seq.word, int)seq.word 

Export _(seq.int, int)int 

Export _(s:pseq.seq.word, i:int)seq.word 

Export _(pseq.int, int)int 

Export _(a:pseq.word, b:int)word 

Export length(seq.word)int 

Export length(seq.seq.word)int 

Export length(seq.int)int 

Export findindex(word, seq.word)int 

/Export findindex(seq.word, seq.seq.word)int 

Export findindex(word, seq.word, int)int 

Export identity(seq.word)seq.word 

Export identity(word)word 

Export identity(int)int 

Export last(s:seq.word)word 

Export subseq(seq.seq.word, int, int)seq.seq.word 

Export subseq(seq.word, int, int)seq.word 

Export subseq(seq.int, int, int)seq.int 

Export in(word, seq.word)boolean 

Export in(seq.word, seq.seq.word)boolean 

Export in(int, seq.int)boolean 

Export =(seq.word, seq.word)boolean 

Export =(seq.int, seq.int)boolean 

Export +(seq.word, word)seq.word 

Export +(seq.int, seq.int)seq.int 

Export +(seq.int, int)seq.int 

Export last(seq.int) int 

Export +(seq.seq.word, seq.word)seq.seq.word 

Export +(seq.seq.word, seq.seq.word)seq.seq.word 

Export +(a:seq.word, b:seq.word)seq.word 

Export nbspchar char 


Export alphasort(a:seq.word)seq.word  


Export alphasort(a:seq.seq.word)seq.seq.word 

type char is record toint:int

Function =(a:char,b:char) boolean toint.a=toint.b

Function ?(a:char,b:char) ordering toint.a ? toint.b

Function hash(a:char) int hash.toint.a


Export type:char  

Export type:seq.char 

Function length(seq.char) int export

Function empty:seq.char seq.char export

Export +(seq.char, seq.char) seq.char  

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
  stdlib exclude stdlib seq  




* usegraph include  prims   tree  graph ipair libscope internalbc
process stack set   format groupparagraphs    bitpackedseq maindict worddict
exclude stdlib seq 

* usegraph include  main2 libscope display constant codegen convert 
 parse pass1  symbol libdesc
codetemplates pass2 persistant   llvm  postbind
reconstruct persistantseq opt2
symbol parse libdesc internalbc intercode cvttoinst codegen pass2new codegennew funcsig
exclude seq set otherseq stdlib bits tree graph UTF8 stack stacktrace real process  ipair 
bitpackedseq   fileio   textio encoding words 
   


