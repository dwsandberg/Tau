
Module libdesc

use stdlib

use symbol

use seq.symbol

use set.symbol

use seq.firstpass



use seq.seq.int



use seq.seq.word

use seq.word


use set.word

use seq.int


use seq.libmod

use seq.mytype

use encoding.seq.char

use seq.encodingrep.seq.char

use seq.myinternaltype


 Function libdesc(p:program,templates:program,mods:seq.firstpass,exports:seq.word,rootsigs:seq.symbol) symbol
  let closed=toexport(p,empty:set.symbol,asset.rootsigs)  
   let d=@(+,tolibsym(p,templates),empty:seq.symbol,toseq.closed )    
    let libmods=  @(+,tolibmod(p,templates,exports),empty:seq.libmod,mods)
       + libmod(false,"$other"_1, d, empty:seq.symbol, empty:seq.mytype)
addseq.@(+,addlibmod,empty:seq.symbol,libmods)
       

 function tolibmod(p:program,templates:program,exports:seq.word,m:firstpass) seq.libmod
  if  not(   abstracttype.modname.m   in exports )  then empty:seq.libmod else
  let abstract=isabstract.modname.m
    let e=@(+,tolibsym(p,templates),empty:seq.symbol,toseq.exports.m)
   let d=if abstract then @(+,tolibsym(p,templates),empty:seq.symbol,toseq.defines.m) else empty:seq.symbol
  [libmod(modname.m,d,e, if abstract then uses.m else empty:seq.mytype)]

function   toexport(p:program,processed:set.symbol, toprocess:set.symbol) set.symbol
   if isempty.toprocess then  processed else 
    let q= asset.@(+,exportcode.p,empty:seq.symbol,     toseq.toprocess)
      toexport(p,processed &cup toprocess, q-processed)

      
  
  Function exportcode(p:program,s:symbol) seq.symbol
    if fsig.s="wordencoding" &and module.s="words"  then  empty:seq.symbol
    else 
      let code=code.lookupcode(p, s)
          if length.code  < 15 then code else empty:seq.symbol
             
             
 / function   sigtosyms(p:prg,s:sig) seq.symbol
            let f=decode.s
              if module.f ="$fref" then 
                [Fref.sigtosyms(p,(constantcode.f)_1)_1]
              else if module.f = "$constant" then
               @(+,sigtosyms.p,empty:seq.symbol,constantcode.f)+Record.length.constantcode.f
              else [tosymbol.s]
                     
function tolibsym(p:program,templates:program,sym:symbol ) seq.symbol
    if module.sym in ["$","$constant","int $","local","$word","$words","$fref"] 
    then empty:seq.symbol else
    if isabstract.mytype.module.sym then 
     let t=lookupcode(templates,sym)
              [ symbol(fsig.sym,module.sym, returntype.sym ,[sym]+code.t )]
    else 
      let code=exportcode(p,sym )
                  [ symbol(fsig.sym,module.sym, returntype.sym ,[sym]+code )]
   

----------------------------------

function addlibsym(s:symbol) symbol
      constant.[Words.fsig.s ,Words.module.s ,Words.returntype.s ,addseq.@(+,addlibsym,empty:seq.symbol,zcode.s),Lit.0]

function addmytype(t:mytype) symbol  Words.(towords.t)

use seq.mytype

function addseq(s:seq.symbol) symbol  
constant.([ Lit.0, Lit.length.s ]+s )

function addlibmod(s:libmod) symbol 
    constant.[Lit.if isabstract.modname.s then 1 else 0
     ,Word.abstracttype.modname.s
     ,addseq.@(+,addlibsym,empty:seq.symbol,defines.s)
      ,addseq.@(+,addlibsym,empty:seq.symbol,exports.s)
    ,addseq.@(+,addmytype,empty:seq.symbol,uses.s)]


--------------------------

Function type:liblib internaltype export


Function type:libmod internaltype export



type liblib is record libname:seq.word, words:seq.encodingrep.seq.char, mods:seq.libmod, timestamp:int, readonly:boolean

Function liblib(a:seq.word, d:seq.libmod)liblib liblib(a, empty:seq.encodingrep.seq.char, d, 0, false)

Function timestamp(liblib)int export

Function libname(liblib)seq.word export

Function mods(liblib)seq.libmod export

Function words(liblib)seq.encodingrep.seq.char export

Function readonly(liblib)boolean export


use otherseq.word


function =(a:libmod, b:libmod)boolean modname.a = modname.b

Function uses(libmod)seq.mytype export

Function loadedlibs seq.liblib builtin.usemangle


type libmod is record parameterized:boolean, modnamex:word, defines:seq.symbol, exports:seq.symbol, uses:seq.mytype

Function libmod(parameterized:boolean, modname:word, defines:seq.symbol, exports:seq.symbol, uses:seq.mytype)libmod export

Function libmod(modname:mytype, defines:seq.symbol, exports:seq.symbol, uses:seq.mytype)libmod 
 libmod(isabstract.modname,abstracttype.modname,defines,exports,uses)
 
Function modname(l:libmod)mytype  mytype.if parameterized.l then  "T"+modnamex.l else [modnamex.l]


Function defines(l:libmod)seq.symbol export

Function exports(l:libmod)seq.symbol export


use seq.firstpass
        
function tofirstpass(m:libmod)  seq.firstpass
 [ firstpass( modname.m , uses.m,   asset.defines.m, asset.exports.m , empty:seq.symbol, empty:set.symbol,
 @(+,libtypes,empty:seq.myinternaltype,defines.m))]
 
  function alllibsym(l:liblib) seq.symbol   @(+,defines, empty:seq.symbol,mods.l)+@(+,exports, empty:seq.symbol,mods.l)

 Function otherlibsyms(dict:set.symbol,l:seq.liblib) program   
  program(asset.@(+,alllibsym, empty:seq.symbol,l)-knownlibsyms.l)
  
        function knownlibsyms(l:liblib) seq.symbol   defines.last.mods.l
        
        function knownlibsyms(l:seq.liblib) set.symbol asset.@(+,knownlibsyms, empty:seq.symbol,l)


function addfirstpass(s:seq.firstpass,l:seq.liblib) seq.firstpass  
  if isempty.l then s else  s+@(+, tofirstpass, empty:seq.firstpass, mods.l_1)

function addfirstpass(l: liblib) seq.firstpass  
 @(+, tofirstpass, empty:seq.firstpass, mods.l)

  
Function dependentlibs(dependentlibs:seq.word)   seq.liblib @(+,filter(dependentlibs),empty:seq.liblib   , loadedlibs)


Function libsymbols(dict:set.symbol,l:seq.liblib) program 
@(addknown.dict,identity,emptyprogram,l) 
 

function addknown(dict:set.symbol,p:program,l:liblib) program 
  program(toset.p &cup asset.defines.last.mods.l)
  
 @(addlibsym.dict,  identity, p, defines.last.mods.l)


use seq.liblib


  function libtypes(     s:symbol) seq.myinternaltype
     if not(returntype.s="internaltype") then empty:seq.myinternaltype
     else
       let code= @(+,removeconstant,empty:seq.symbol,if last.zcode.s=Optionsym then subseq(zcode.s,1,length.zcode.s-2) else  zcode.s)
     let l=length.code
     // assert not(fsig.s=[merge("type:boolean")]) report "here"+@(+,print,print.s,code)+"&br"
     +returntype.s+fsig.code_l+(fsig.code_(l-1))_1  //
     if fsig.code_l="RECORD 5" &and (fsig.code_(l-1))_1="RECORD"_1 then
      let noflds=toint.(fsig.code_(l-1))_2-2
      let t1=subseq(code,l-noflds-1,l-2)
      let subflds=@(+,mytype,empty:seq.mytype,@(+,fsig,empty:seq.seq.word,t1))
      let size=value.code_2
      let kind=fsig.code_3
      let name=fsig.code_4
      let modname=fsig.code_5
      [myinternaltype(size,kind_1,name_1,mytype.modname,subflds)]
     else empty:seq.myinternaltype

function removeconstant(s:symbol) seq.symbol
if module.s="$constant" then @(+,removeconstant,empty:seq.symbol,zcode.s)+Record.length.zcode.s
else [s]
  

Function libfirstpass(l:seq.liblib) seq.firstpass
  @(+,addfirstpass, empty:seq.firstpass   , l)

function filter(s:seq.word,l:liblib)  seq.liblib   if (libname.l)_1 in s then [l] else empty:seq.liblib
    












   
 