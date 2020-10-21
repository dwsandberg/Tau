
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


use seq.firstpass

use seq.mytype

use encoding.seq.char

use seq.encodingpair.seq.char

use seq.myinternaltype


 Function libdesc(pin:program,templates:program,mods:seq.firstpass,exports:seq.word,rootsigs:seq.symbol) symbol
  let p=  pin &cap asset.rootsigs
  let closed=@(+,filterbuiltin,empty:seq.symbol,toseq.asset.@(+,exportcode.p, rootsigs, rootsigs) )
  let d=@(+,tolibsym(p,templates),empty:seq.symbol, closed )     
    let libmods=  @(+,tolibmod(p,templates,exports),empty:seq.firstpass,mods)
       + libmod(mytype."$other" , d, empty:seq.symbol, empty:seq.mytype)
addseq.@(+,addlibmod,empty:seq.symbol,libmods)

 
 function   filterbuiltin(s:symbol) seq.symbol if isbuiltin.module.s then empty:seq.symbol else [s]

 function tolibmod(p:program,templates:program,exports:seq.word,m:firstpass) seq.firstpass
  if  not(   abstracttype.modname.m   in exports )  then empty:seq.firstpass else
  let abstract=isabstract.modname.m
    let e=@(+,tolibsym(p,templates),empty:seq.symbol,toseq.exports.m)
   let d=if abstract then @(+,tolibsym(p,templates),empty:seq.symbol,toseq.defines.m) else empty:seq.symbol
  [libmod(modname.m,d,e, if abstract then uses.m else empty:seq.mytype)]
      
  
  Function exportcode(p:program,s:symbol) seq.symbol
       let code=code.lookupcode(p, s)
          if length.code  < 15 then removeconstant.code else empty:seq.symbol
             
             
function tolibsym(p:program,templates:program,sym:symbol ) seq.symbol
    if isconstantorspecial.sym 
    then empty:seq.symbol else
    let cleansym= [if isempty.zcode.sym then sym else symbol(fsig.sym,module.sym,returntype.sym)]
    let code=if isabstract.mytype.module.sym then 
      code.lookupcode(templates,sym)
     else 
      removeconstant.exportcode(p,sym )
                  [ symbol(fsig.sym,module.sym, returntype.sym ,cleansym+code )]
   

----------------------------------

function addlibsym(s:symbol) symbol
      Constant2.[Words.fsig.s ,Words.module.s ,Words.returntype.s ,
      addseq.@(+,addlibsym,empty:seq.symbol,zcode.s),Lit.extrabits.s 
      ,Record.[mytype."ptr",mytype."ptr",mytype."ptr",mytype."ptr",mytype."int"]]

function addmytype(t:mytype) symbol  Words.(towords.t)

use seq.mytype

use otherseq.mytype

function addseq(s:seq.symbol) symbol  
Constant2.([ Lit.0, Lit.length.s ]+s+Record( [mytype."int",mytype."int"]+constantseq(length.s,mytype."ptr") ))

function addlibmod(s:firstpass) symbol 
    Constant2.[addmytype.modname.s
     ,addseq.@(+,addmytype,empty:seq.symbol,uses.s)
     ,addseq.@(+,addlibsym,empty:seq.symbol,toseq.defines.s)
      ,addseq.@(+,addlibsym,empty:seq.symbol,toseq.exports.s)
      ,Words."" ,Words."" ,Words.""
      ,Record.[mytype."ptr",mytype."ptr",mytype."ptr",mytype."ptr",mytype."ptr",mytype."ptr",mytype."ptr"]
]


--------------------------

Function type:liblib internaltype export

Function type:parc internaltype export

type liblib is record libname:seq.word, words:seq.encodingpair.seq.char, mods:seq.firstpass, timestamp:int, profiledata:seq.parc

type parc is record head:word, tail:word, counts:int, clocks:int, space:int

function parc(head:word, tail:word, counts:int, clocks:int, space:int) export

Function head(parc)word export

Function tail(parc)word export

Function counts(parc)int export

Function clocks(parc)int export

Function space(parc)int export


Function timestamp(liblib)int export

Function libname(liblib)seq.word export

Function mods(liblib)seq.firstpass export

Function words(liblib)seq.encodingpair.seq.char export

Function profiledata(liblib)seq.parc export


use otherseq.word


 
Function loadedlibs seq.liblib builtin.usemangle


 
Function libmod(modname:mytype, defines:seq.symbol, exports:seq.symbol, uses:seq.mytype)firstpass 
  firstpass(modname ,  uses , asset.defines , asset.exports , empty:seq.symbol, 
empty:set.symbol,empty:seq.myinternaltype)


 

use seq.firstpass
        
function tofirstpass(m:firstpass)  seq.firstpass
 [ firstpass( modname.m , uses.m,    defines.m,  exports.m , empty:seq.symbol, empty:set.symbol,
 @(+,libtypes,empty:seq.myinternaltype,toseq.defines.m))]
 
  function alllibsym(l:liblib) seq.symbol   toseq.(@(&cup,defines, empty:set.symbol,mods.l) &cup @(&cup,exports, empty:set.symbol,mods.l))

 Function otherlibsyms(dict:set.symbol,l:seq.liblib) program   
  program(asset.@(+,alllibsym, empty:seq.symbol,l)-knownlibsyms.l)
  
        function knownlibsyms(l:liblib) seq.symbol   toseq.defines.last.mods.l
        
        function knownlibsyms(l:seq.liblib) set.symbol asset.@(+,knownlibsyms, empty:seq.symbol,l)


function addfirstpass(s:seq.firstpass,l:seq.liblib) seq.firstpass  
  if isempty.l then s else  s+@(+, tofirstpass, empty:seq.firstpass, mods.l_1)

function addfirstpass(l: liblib) seq.firstpass  
 @(+, tofirstpass, empty:seq.firstpass, mods.l)

  
Function dependentlibs(dependentlibs:seq.word)   seq.liblib @(+,filter(dependentlibs),empty:seq.liblib   , loadedlibs)


Function libsymbols(dict:set.symbol,l:seq.liblib) program 
@(addknown.dict,identity,emptyprogram,l) 
 

function addknown(dict:set.symbol,p:program,l:liblib) program 
  program(toset.p &cup defines.last.mods.l)
  
 

use seq.liblib


  function libtypes(     s:symbol) seq.myinternaltype
     if not(returntype.s="internaltype") then empty:seq.myinternaltype
     else
       let code=     zcode.s 
       let l=length.code-if last.zcode.s=Optionsym  then 2 else 0 
       if    isrecord.code_l &and nopara.code_l=5 &and (fsig.code_(l-1))_1="RECORD"_1 then
      let noflds=nopara.code_(l-1)-2
      let t1=subseq(code,l-noflds-1,l-2)
      let subflds=@(+,mytype,empty:seq.mytype,@(+,fsig,empty:seq.seq.word,t1))
      let size=value.code_2
      let kind=fsig.code_3
      let name=fsig.code_4
      let modname=fsig.code_5
      [myinternaltype(size,kind_1,name_1,mytype.modname,subflds)]
     else empty:seq.myinternaltype

function removeconstant(s:seq.symbol) seq.symbol
@(+,removeconstant,empty:seq.symbol, s) 

function removeconstant(s:symbol) seq.symbol
if module.s="$constant" then  removeconstant.zcode.s  
else [s]
  

Function libfirstpass(l:seq.liblib) seq.firstpass
  @(+,addfirstpass, empty:seq.firstpass   , l)

function filter(s:seq.word,l:liblib)  seq.liblib   if (libname.l)_1 in s then [l] else empty:seq.liblib
    












   
 