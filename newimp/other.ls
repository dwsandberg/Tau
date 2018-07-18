#!/usr/local/bin/tau

 
Module other

run other test1

use stdlib

use stack.stkele

use seq.stkele

use seq.stepresult

use seq.mytype

use set.symbol

use seq.symbol

use borrow


use seq.moddesc

use  process.bindinfo

use newimp

use pass2

use set.symbol

use seq.firstpass

  
 use set.word
 
 use Symbol
 
  
 use seq.seq.word
 
 use blockseq.int
  
function dcopy(i:int) int i

Function test1 seq.word
  X("small")
 

type   firstpass is record modname:mytype, uses:seq.mytype,defines:set.symbol,exports:set.symbol,unboundexports:seq.symbol,
unbound:set.symbol,exportmodule:boolean


function exportmodule(firstpass) boolean export

function modname(firstpass) mytype export

function defines(firstpass) set.symbol export

function exports(firstpass) set.symbol export

Function replaceT(with:mytype,f:firstpass) firstpass
  firstpass(replaceT(with,modname.f), @(+, replaceT.with, empty:seq.mytype, uses.f),
    asset.@(+, replaceT.with, empty:seq.symbol, toseq.defines.f),
    asset.@(+, replaceT.with, empty:seq.symbol, toseq.exports.f),
    @(+, replaceT.with, empty:seq.symbol, unboundexports.f),asset.@(+, replaceT.with, empty:seq.symbol, toseq.unbound.f),false)
    

function =(a:firstpass,b:firstpass) boolean  modname.a=modname.b

function ?(a:firstpass,b:firstpass) ordering modname.a ? modname.b

function   print(b:firstpass) seq.word "&br &br "+print.modname.b
  +"&br defines"+ printdict.defines.b
  +"&br unboundexports"+ printdict.asset.unboundexports.b

function find(modset:set.firstpass, name:mytype) set.firstpass
 findelement(firstpass(name,empty:seq.mytype,empty:set.symbol,empty:set.symbol,empty:seq.symbol,empty:set.symbol,false),modset)
 



use seq.symbol



function X(libname:seq.word)seq.word 
 let ld=tolibdesc(libname_1)
 let a = @(+, gathersymbols(exports.ld), empty:set.firstpass, modules.ld)
 let d2=resolveunboundexports.expanduse.a 
 let simple=@(+,findsimple,empty:seq.firstpass,toseq.d2)
 let roots= toseq.asset.@(+,roots,"",simple)
 let abstractmods=@(+,templates(d2),empty:seq.firstpass,toseq.d2)
  let templates= @(+,identity,  emptysymbolset,toseq.@(&cup,defines,empty:set.symbol,abstractmods))
 let knownsymbols=@(+,identity,emptysymbolset,toseq.@(&cup,defines,empty:set.symbol,simple)) 
 let X=@(bind(templates,d2),identity,  knownsymbols ,simple )
      testrt(X,roots) 
   
 PARAM 1 lengthZalphawordzseqzseqZTzseq LIT 0 
 Q3DZbuiltinZintZint PARAM 1 PARAM 1 lengthZalphawordzseqzseqZTzseq LIT 0 
 Q3DZbuiltinZintZint PARAM 1 PARAM 1 LIT 1 Q5FZalphawordzseqzseqZTzseqZint PARAM 1 PARAM 1 lengthZalphawordzseqzseqZTzseq Q5FZalphawordzseqzseqZTzseqZint 
 Q3FZalphawordzoseqZTzseqZTzseq GTZstdlib 
 Q3DZstdlibZorderingZordering PARAM 1 PARAM 1 Q2BZalphawordzseqzseqZTzseqZTzseq PARAM 1 LIT 1 Q5FZalphawordzseqzseqZTzseqZint PARAM 1 PARAM 1 lengthZalphawordzseqzseqZTzseq Q5FZalphawordzseqzseqZTzseqZint 
 Q3FZalphawordzoseqZTzseqZTzseq GTZstdlib 
 Q3DZstdlibZorderingZordering PARAM 1 PARAM 1 Q2BZalphawordzseqzseqZTzseqZTzseq PARAM 1 PARAM 1 LIT 1 LIT 1 submergeZalphawordzseqzoseqZTzseqZTzseqZintZint if if if if

 
function recordsize( src:seq.word, i:int) int
  // bug if made tail recursive ? //
   if i > length.src then 0
   else if i=1 &and src_i="FREF"_1 then recordsize(src,i+2)+1
   else if src_i ="PARAM"_1 then recordsize(src,i+2)+1
    else if src_i ="LIT"_1 then recordsize(src,i+3)
   else 10000
 
     
function  removeflat( p:word,i:int) seq.word
        if i=0 then "" else 
        removeflat(p,i-1)+"PARAM"+p+"LIT"+toword.i+"IDXUC"
       
       

function resolveunboundexports(modset:set.firstpass) set.firstpass
    let u = @(+,hasunbound,empty:seq.firstpass,toseq.modset)
   let orgcount= @(+,totalunbound,0,u)
   if orgcount = 0 then modset else 
   let newset=@(bindunboundexports,identity,modset,u)
   let newcount=@(+,totalunbound,0,toseq.newset)
   if newcount = orgcount then modset
   else resolveunboundexports(newset)
 
 
function builddict(modset:set.firstpass, use:mytype) set.symbol
     let e=find(modset,use)
     if isempty.e then empty:set.symbol else
     exports.find(modset,use)_1

function builddict(modset:set.firstpass,f:firstpass) set.symbol
 @(&cup,  builddict(modset),defines.f &cup unbound.f,uses.f)

 
 function bindunboundexports(modset:set.firstpass,f:firstpass) set.firstpass
   if length.unboundexports.f=0 then modset else
   let dict=builddict(modset,f)
   let new=  @(resolveexport.dict,identity,firstpass(modname.f,uses.f,defines.f,exports.f, empty:seq.symbol,unbound.f,exportmodule.f), unboundexports.f)
        replace(modset,new)
         
function resolveexport(dict:set.symbol,f:firstpass, s:symbol) firstpass
  let x=findelement2(dict, s) 
 if cardinality.x=1 then 
   firstpass(modname.f,uses.f,defines.f,exports.f &cup x,unboundexports.f,unbound.f,exportmodule.f)
else firstpass(modname.f,uses.f,defines.f,exports.f,unboundexports.f+s,unbound.f,exportmodule.f)

         
function expanduse( modset:set.firstpass) set.firstpass
    let newset=@( expanduse, identity, modset,toseq.asset.@(+,uses,empty:seq.mytype,toseq.modset))
    if cardinality.newset > cardinality.modset then expanduse(newset)
    else modset
     

function expanduse(modset:set.firstpass,use:mytype) set.firstpass
      if  iscomplex.use &and not(parameter.use =mytype."T") then
       let x= find(modset,use )  
       if isempty.x then
          let  template = find(modset,mytype("T"+abstracttype.use))
          assert not.isempty.template report "Cannot find module"+print.use
          modset+ replaceT(parameter.use,template_1)
       else modset
      else modset

         
    
    
function hasunbound(f:firstpass) seq.firstpass
 if length.unboundexports.f=0 then empty:seq.firstpass
 else [f]
 
 function totalunbound(f:firstpass) int
  length.unboundexports.f 
 


function findsimple(f:firstpass) seq.firstpass 
   if length.towords.modname.f=1 then [f] else empty:seq.firstpass
   



function templates(modset:set.firstpass,f:firstpass) seq.firstpass
   if parameter.modname.f=mytype."T" then  
    let newdefines=@(+,template(builddict(modset,f) &cup headdict),empty:seq.symbol,toseq.defines.f)
    [firstpass(modname.f, empty:seq.mytype,asset.newdefines ,exports.f,empty:seq.symbol,empty:set.symbol,exportmodule.f)]
   else empty:seq.firstpass


function    template(dict:set.symbol,s:symbol) symbol
      if (src.s)_1 in "type sequence record encoding LIT"  then
        s
      else 
           let b=parse(bindinfo(dict,"",empty:seq.mytype),src.s) 
            changesrc(s,code.b)

function bind(templates:symbolset,modset:set.firstpass,a:symbolset,f:firstpass) symbolset
  let x=subseq(towords.modname.f,1,length.towords.modname.f-1)
  if  x="" then
     let z=@(+,iscomplex,empty:seq.symbol,toseq.exports.f)
      // assert length.z=0 report "PP"+@(+,print,"",z)  //
      let dict=builddict(modset,f) &cup headdict
      let b=@(x2(templates,dict),identity,a,toseq.exports.f)
      @(bind(templates,dict),identity,b,toseq.defines.f)
  else if x="T" then
         @(bind(templates,builddict(modset,f) &cup headdict),identity,a,toseq.defines.f)
    else a 
    
function iscomplex(s:symbol) seq.symbol 
  if iscomplex.modname.s then [s] else empty:seq.symbol 

function x2(templates:symbolset,dict:set.symbol,knownsymbols:symbolset,s:symbol) symbolset
     if iscomplex.modname.s then 
     let x=known.X(mangledname.s,s,dict, parameter.modname.s,templates,knownsymbols)
    //  let a=x_mangledname.s
      assert mangledname.s &ne "Q5FZintzseqZTzcseqZint"_1 report "HERE"
      assert isdefined.a report "XX"+print2.a //
      x
      else knownsymbols

 X(code_i,   org ,dict,modpara,templates,knownsymbols)
    
function bind(templates:symbolset,dict:set.symbol,knownsymbols:symbolset,s:symbol) symbolset
     if (src.s)_1 in "type sequence record encoding LIT"  then
       postbind(dict,mytype."",templates,knownsymbols,src.s,s,s) 
    else 
      assert length.src.s > 2  report "PROBLEM TT"
       let b=parse(bindinfo(dict,"",empty:seq.mytype),src.s) 
       postbind(dict,mytype."",templates,knownsymbols,code.b,s,s) 
       
type  zzz is record known:symbolset, size:seq.word

      
function buildtypedesc(knownsymbols:symbolset,k:seq.word,t:mytype) seq.word
   k+if abstracttype.t in "word int seq" then  print.t
   else if abstracttype.t="encoding"_1 then "int"
   else 
                    let name=mangle(merge(" typedesc:"+print.t),mytype."internal",empty:seq.mytype)
                  let a = knownsymbols_name
                  assert not(mangledname.a="undefinedsym"_1) report "type?"+name+print.t 
                   src.a
 

         
function definestructure(org:symbol,dict:set.symbol,templates:symbolset,src:seq.word, modname:mytype, knownsymbols:symbolset,i:int,offset:seq.word
,paras:seq.mytype,constructor:seq.word) symbolset
//  defines function to work with types record and sequence //
     if i > length.src then  
       let consrc=if length.paras=1 then "PARAM 1 VERYSIMPLE" else   constructor+"RECORD"+toword.recordsize(constructor,1)
       let con=symbol(src_2,modname,paras,mytype(towords.parameter.modname  +src_2),consrc)
       let name= merge("sizeoftype:"+ if towords.parameter.modname="" then [src_2] else print.mytype("T"  +src_2))
       if src_1="sequence"_1 then
          let sizesym=  symbol(name,modname,empty:seq.mytype,mytype."int",  "LIT 1" ) 
          let t =  mytype.(towords.parameter.modname+src_2 )
          let symtoseq=symbol("toseq"_1, modname, [ mytype.("T"+src_2 )], mytype(towords.parameter.t +"seq"_1),"PARAM 1 VERYSIMPLE")
          // assert  not (src_2="pseq"_1 &and print.modname="seq.word") report print.modname+src+"&br"+print2.symtoseq //
           replace(replace(replace(knownsymbols,con),sizesym),symtoseq)
       else  
          let  dsrc=
             @(buildtypedesc.knownsymbols,replaceT.parameter.modname,"",paras)
         let descsym= symbol(merge(" typedesc:"+print.resulttype.con),mytype."internal",empty:seq.mytype,mytype."word seq",  dsrc )
          let sizesym=  symbol(name,modname,empty:seq.mytype,mytype."int",offset)
                             // assert not(print.resulttype.con="ipair.word") report "JJJ"+mangledname.sizesym+mangledname.descsym //
           replace(replace(replace(knownsymbols,con),sizesym),descsym) 
  else 
    let len=  (toint.src_i) 
    let a = mytype.subseq(src,i+1,i+len-1)
    let fldtype=mytype.subseq(src,i+1,i+len-1)    
    let thetype=replaceT(parameter.modname,fldtype)
    let z1=if abstracttype.thetype in "int real seq  word encoding"  
         then   
            zzz(knownsymbols,"LIT 1" )
         else         
           let x=lookup(dict,merge("sizeoftype:"+print.thetype),empty:seq.mytype )
          assert  not.isempty.x report "HJKL:"+print.thetype+ print.org 
          let z1 = X(mangledname.x_1,   org ,dict,parameter.modname.x_1,templates,knownsymbols) 
          let newknown=known.z1   
          if length.size.z1=2 &and (size.z1)_1="LIT"_1  then z1 
          else
             let z=newknown_(mangledname.x_1)  
             assert isdefined.z report "KL"+mangledname.x_1
             let symsrc=src.z
             assert  length.symsrc=2 &and (symsrc)_1="LIT"_1 report "KL2"+print2.z+print.thetype
             zzz(newknown,symsrc )  
    let newoffset=   if offset="" then size.z1   else  "LIT"+toword(toint.offset_2+toint.(size.z1)_2 )
    let fldsrc= if offset="" then "PARAM 1" else  "PARAM 1"+offset+"IDXUC"
    let ptype=if parameter.modname=mytype."" then [src_2 ] else "T"+src_2
    let fldsym=   symbol(src_(i+len),modname,[mytype(ptype)],fldtype,fldsrc)
    let confld=if size.z1="LIT 1" then "PARAM"+toword(  length.paras+1)else
      "PARAM"+toword(  length.paras+1)+ if size.z1="LIT 1" then "" else 
          removeflat(toword(  length.paras+1),toint.(size.z1)_2 -1)  
   definestructure(org,dict,templates,src,modname,replace(known.z1,fldsym) ,i+len+1,newoffset,paras+fldtype ,constructor+confld)
  
function postbind(dict:set.symbol,modpara:mytype,templates:symbolset,knownsymbols:symbolset,code:seq.word, 
thissymbol:symbol,org:symbol 
) symbolset
  // assert not(mangledname.thissymbol="Q2BZwordzseqZTzseqZTzseq"_1) report "GOT HERE"+code //
     if code_1 in "sequence" then 
                   let x=lookup(dict,"_"_1,[mytype(towords.modpara  +code_2),mytype."int"])
                   assert not.isempty.x report "cannot find index function for"+print.mytype(towords.modpara  +code_2)+"in"+print.org
            let newknown=   postbind2(org,dict,modpara,templates,knownsymbols,[mangledname.x_1],1,"",thissymbol)  
         definestructure(org,dict,templates,code,modname.thissymbol,newknown,3, "LIT 1" ,empty:seq.mytype, "FREF"+mangledname.x_1)
    else if code_1 in "record" then 
         definestructure(org,dict,templates,code,modname.thissymbol,replace(knownsymbols,changesrc(thissymbol,"pending")) ,3, "" ,empty:seq.mytype,"")
     else 
     if code_1 in "encoding" then
        let encodingtype= mytype.subseq(code,4,length.code-1)
               // assert  mangledname.thissymbol in "wordencodingZstdlib " report code+ "MMM"+print2.thissymbol  +print.encodingtype //
     let sizeofsym=symbol(merge( "sizeoftype:encoding."+print.encodingtype),modname.thissymbol,empty:seq.mytype,mytype."int","LIT 1")
     let lkup= lookup(dict,"lookup"_1, [encodingtype, mytype.(towords.encodingtype+"invertedseq")] )
     assert not.isempty.lkup  report "not lookup for  "+ code_2+print.encodingtype 
     let iadd= lookup(dict,"add"_1, [mytype.(towords.encodingtype+"invertedseq"),mytype."int",encodingtype] )
     assert not.isempty.iadd  report "not add for  "+ code_2+print.encodingtype 
     let copy=lookup(dict,"dcopy"_1, [encodingtype] )
     assert not.isempty.copy report "no dcopy for  "+ code_2+print.encodingtype  
     let newsrc= if print.encodingtype in ["seq.int"] then  "FREF"+mangledname.copy_1 else  "LIT 1"
         +"FREF"+mangledname.lkup_1
         +"FREF"+mangledname.iadd_1
         +(if name.thissymbol ="wordencoding"_1 then"LIT 1"else"LIT 0")
         +"WORD"+ mangledname.thissymbol + "LIT 3 IDXUC"
         +(if code_1 ="encoding"_1 then"LIT 0" else"LIT 1") 
         + "WORDS"+ toword.length.towords.encodingtype +towords.encodingtype +"RECORD 7 NOINLINE "
     let newknown=   postbind2(org,dict,modpara,templates,knownsymbols,[mangledname.lkup_1,mangledname.iadd_1],1,"",thissymbol)  
        replace(replace(newknown,changesrc(thissymbol,newsrc)),sizeofsym)
     else if last.code="builtinZtestZinternal1"_1 then 
        if code="NOOPZtest builtinZtestZinternal1" then 
               replace(knownsymbols,changesrc(thissymbol,"PARAM 1 VERYSIMPLE"))
        else if code="EMPTYSEQ51Ztest builtinZtestZinternal1 " then
               replace(knownsymbols,changesrc(thissymbol,"LIT 0 LIT 0 RECORD  2 VERYSIMPLE"))
        else if code="CALLIDXZtest builtinZtestZinternal1 " then
               replace(knownsymbols,changesrc(thissymbol,"PARAM 1 PARAM 2 PARAM 3 CALLIDX VERYSIMPLE"))
        else if code="IDXUCZtest  builtinZtestZinternal1 "  then 
          replace(knownsymbols,changesrc(thissymbol,"PARAM 1 PARAM 2  IDXUC VERYSIMPLE"))
        else if  code="FROMSEQ51Ztest builtinZtestZinternal1 " then
              let x=lookup(dict,"_"_1,[resulttype.thissymbol,mytype."int"])
                   assert not.isempty.x report "cannot find index function for"+print.resulttype.thissymbol+"in"+print.org
          let f1 = "PARAM 1 LIT 0 IDXUC FREF"+mangledname.x_1 +" Q3DZbuiltinZintZint  PARAM 1  LIT 0 LIT 0   RECORD  2 if   "
         replace(knownsymbols,changesrc(thissymbol,f1))
        else if  code ="usemangleZtest builtinZtestZinternal1" 
            &or code="usemangleZtest STATEZtestZinternal1 builtinZtestZinternal1" then 
              let builtinname=mangle(name.thissymbol, mytype."builtin", paratypes.thissymbol)
              let src=if mangledname.thissymbol =builtinname then
                 if length.code=3 then "STATE EXTERNAL " else "EXTERNAL"
              else 
                 @(+,topara ,"", arithseq(length.paratypes.thissymbol,1,1))+   mangle(name.thissymbol, mytype."builtin", paratypes.thissymbol)
            + if length.code=3 then "STATE" else ""
            replace(knownsymbols,changesrc(thissymbol,src))
        else 
          postbind2(org,dict,modpara,templates,knownsymbols,code,1,"",thissymbol) 
else if last.code="builtinZtestZwordzseq"_1 &and   (code)_1="WORDS"_1 then 
             replace(knownsymbols,changesrc(thissymbol,subseq(code,3,length.code-1)))
    else postbind2(org,dict,modpara,templates,knownsymbols,code,1,"",thissymbol) 
      
function topara(i:int) seq.word "PARAM"+toword.i 
       
function postbind2(org:symbol ,dict:set.symbol,modpara:mytype,templates:symbolset,knownsymbols:symbolset,code:seq.word,i:int,result:seq.word,
thissymbol:symbol 
) symbolset
      if i > length.code then  
       let src=result
       let nopara=nopara.thissymbol
       let newflag=if  length.src  < 8 * nopara &and  subseq(src,1,2 * nopara)=@(+,topara,"",arithseq(nopara,1,1)) 
  &and not( "PARAM"_1 in subseq(src,nopara * 2 + 1,length.src))
  &and not( mangledname.thissymbol  in src) 
  &and not( "SET"_1 in src)     then "VERYSIMPLE"
 else ""
         replace(knownsymbols,changesrc(thissymbol, result+newflag))
     else 
        if code_i in ("builtinZtestZinternal1  
       IDXUCZtestZint if ?  assertZbuiltinZwordzseq EQ51LZtest  undefine ERECORDZtest NOINLINEZtestZinternal1
       STATEZtestZinternal1 NOINLINEZtest PROFILEZtest FORCEINLINEZtest TESTOPTZtest
          FROMSEQ51Ztest DEEPCOPYZtest" 
        )then 
         postbind2(org,dict,modpara,templates, knownsymbols ,code,i+1,result+code_i,thissymbol)
        else if code_i= "siQ7AeoftypeQ3ATZtest"_1 then
          let size= if print.modpara in ["int","seq.int","bits","seq.bits"] then "LIT 1"
           else 
           assert false report "type size"+print.modpara
           "?"
         postbind2(org,dict,modpara,templates, knownsymbols ,code,i+1,result+size,thissymbol)           
        else  if code_i="FREF"_1   then
                      postbind2(org,dict,modpara,templates, knownsymbols ,code,i+1,result+code_i,thissymbol)       
        else   if code_i="WORDS"_1 then
           postbind2(org,dict,modpara,templates, knownsymbols ,code,i+2+toint(code_(i+1)),result 
              + subseq(code,i,i+1+toint(code_(i+1))),thissymbol)
       else   if code_i in "define LIT APPLY FREF RECORD SET" then
         postbind2(org,dict,modpara,templates, knownsymbols ,code,i+2,result+subseq(code,i,i+1),thissymbol)
       else    
          let z = X(code_i,   org ,dict,modpara,templates,knownsymbols)        
         postbind2(org,dict,modpara,templates, known.z ,code,i+1,result+size.z,thissymbol)

                 
                 
                 
function X(mangledname:word,   org:symbol ,dict:set.symbol,modpara:mytype,templates:symbolset,knownsymbols:symbolset)         zzz   
   let t1=  knownsymbols_mangledname 
   if isdefined.t1 then 
       let src=src.t1 
       if   length.src=2 &and (src )_1 = "LIT" _1 then zzz(knownsymbols,src)
       else 
         if src_1 in "record encoding"  then
           let down=codedown(mangledname)
           assert length.down_2=1 report "inX"+ print2.t1
            zzz(postbind(dict, mytype.down_2,templates,knownsymbols,src,t1,org),[mangledname])
         else 
          zzz(knownsymbols ,[mangledname])
    else
         let down=codedown(mangledname)
         assert length.down > 1 report "LLLx"+mangledname
         if  last(down_2)="para"_1 then 
           zzz(knownsymbols , "PARAM"+down_2_1)
         else if last(down_2)="local"_1 then  zzz(knownsymbols , "LOCAL"+down_1 )
         else 
           let params=@(+,mytype,empty:seq.mytype, subseq(down,3,length.down))
           let newmodname=replaceT(modpara,mytype.down_2)
           let newmodpara=parameter.newmodname
           assert newmodpara &ne mytype."T" report ">>>"
           let templatename=abstracttype.newmodname
           let fullname=mangle( down_1_1, newmodname    ,params) 
           let t2 = knownsymbols_fullname
            if fullname &ne mangledname &and isdefined.t2   then 
                let src=src.t2
                if (src )_1 in "sequence record" then 
                  zzz(postbind(dict, newmodpara,templates,knownsymbols,src,t2,org),[fullname])
                else 
                  zzz(knownsymbols,[fullname])
           else 
              let t = symbol(down_1_1, mytype("T"+templatename), params, mytype."?","")
              let f= templates_mangledname.t 
               if isdefined.f  then
                  let newsymbol=    symbol(down_1_1, newmodname, params,replaceT(newmodpara,resulttype.f),src.f)
                  let a =postbind(dict, newmodpara,templates,knownsymbols+newsymbol,src.f,newsymbol,org) 
                                                                assert not(mangledname="toseqZTzseqZTzpseq"_1) 
                                                                report "XXXXX"+print.modpara   +print2.a_mangledname.newsymbol
                  zzz(a,[fullname])
               else 
                   let params2=@(+,replaceT(modpara),empty:seq.mytype,params)
                   let k=  lookup(dict,down_1_1,params2) 
                   assert cardinality.k=1 report "cannot find template for"+down_1_1+"("+@(seperator.",",print,"",params2)+") while process"
                   +print.org
                 zzz(knownsymbols ,[mangledname.k_1])               
                 
  
   function roots(f:firstpass ) seq.word                
            if exportmodule.f then @(+,mangledname,"",toseq.exports.f) else ""
            

function gathersymbols(exported:seq.word,m:moddesc) firstpass 
let modulename=mytype."test"
let stubdict=   asset.[        symbol("export"_1,modulename, empty:seq.mytype,mytype."internal",""),
             symbol("unbound"_1,modulename, empty:seq.mytype,mytype."internal",""),
             symbol("stub"_1,modulename, empty:seq.mytype,mytype."internal",""),
             symbol("usemangle"_1,modulename, empty:seq.mytype,mytype."internal","")]
 @(wrapgathersymbols(exported,stubdict), identity,firstpass(mytype."?",empty:seq.mytype,empty:set.symbol,empty:set.symbol,empty:seq.symbol,empty:set.symbol,false),
 src.m) 
 
function wrapgathersymbols(exported:seq.word,stubdict:set.symbol,f:firstpass,input:seq.word) firstpass
let p = process.gathersymbols(exported,stubdict,f,input)
 assert not.aborted.p report message.p+"FAIL"+input
 result.p
 
 
  

use process.firstpass

 
   

function  definefld(src:seq.word,modname:mytype,t:seq.mytype,m:mytype)  symbol
        symbol(abstracttype.m,modname,t,parameter.m,src)
   
   

function gathersymbols(exported:seq.word,stubdict:set.symbol,f:firstpass,input:seq.word) firstpass
// assert print.modname.f in ["?","stdlib","UTF8","altgen"] &or( print.modname.f= "bitpackedseq.T" &and cardinality.defines.f+ cardinality.unbound.f < 8)
 report print.modname.f+printdict.unbound.f //
if input in ["Function sizeoftype T builtin.TYPESIZE ","type encoding"] then f
else if length.input=0 then f 
else if input_1 in "use" then
      let t=parse(empty:set.symbol,input)
      firstpass( modname.f, uses.f+mytype.code.t,defines.f,exports.f,unboundexports.f,unbound.f,exportmodule.f)
  else if input_1 in "type" then 
     if input in ["type int","type real"] then 
      let syms = [symbol(merge("sizeoftype:"+input_2),modname.f,empty:seq.mytype,mytype."int","LIT 1")]
       firstpass(modname.f,uses.f,defines.f &cup asset.syms,exports.f &cup asset.syms,unboundexports.f,unbound.f,exportmodule.f) 
     else 
       let b = parse(empty:set.symbol,input)
       let kind=(code.b)_1
          let t =  mytype.(towords.parameter.modname.f+[(code.b)_2] )
       if kind  = "encoding"_1 then
          let typ=parameter.(types.b)_1
         let sizeofsym=[symbol(merge( "sizeoftype:encoding."+print.typ),modname.f,empty:seq.mytype,mytype."int",code.b)]  
         let syms=          [symbol((code.b)_2,modname.f,empty:seq.mytype, mytype(towords.typ+"erecord"),code.b)]
          firstpass(modname.f,uses.f+mytype(towords.typ+"invertedseq") 
             ,defines.f &cup asset(syms+sizeofsym),exports.f &cup asset.sizeofsym,unboundexports.f,unbound.f,exportmodule.f) 
       else
            let sizeofsym=[symbol(merge("sizeoftype:"+print.t) ,modname.f,empty:seq.mytype,mytype."int",code.b)]  
          let constructor= symbol( (code.b)_2,modname.f,@(+,parameter,empty:seq.mytype,types.b),t,code.b)
         let syms=  @(+,definefld(code.b,modname.f,[t]),[constructor] ,types.b)+  
           if kind="sequence"_1 then
                [symbol("toseq"_1, modname.f, [ t], mytype(towords.parameter.t +"seq"_1),code.b)] 
              else empty:seq.symbol
      firstpass(modname.f,uses.f,defines.f &cup asset(syms+sizeofsym),exports.f &cup asset.sizeofsym,unboundexports.f,unbound.f,exportmodule.f)
 else if input_1 in "Function function" then
    let  t = parse(stubdict,getheader.input)
         let name = (towords.(types.t)_1)_1
     let n=if iscomplex.modname.f &and  length.subseq(types.t,3,length.types.t)=0 
         then merge([name]+":"+print.(types.t)_2) else  name
     if code.t="usemangleZtest"  then
          let sym=symbol(  n,mytype.if iscomplex.modname.f then  "T builtin" else "builtin",
          subseq(types.t,3,length.types.t),(types.t)_2,input)
         firstpass( modname.f, uses.f,defines.f+sym,if  input_1="Function" _1 then exports.f+sym else exports.f,unboundexports.f,unbound.f,exportmodule.f)
      else 
       let sym=symbol(  n,modname.f,subseq(types.t,3,length.types.t),(types.t)_2,input)
      if  "exportZtest"  =  code.t then 
           firstpass( modname.f, uses.f,defines.f,exports.f,unboundexports.f+sym,unbound.f,exportmodule.f)
     else if  "unboundZtest"  =  code.t then 
           firstpass( modname.f, uses.f,defines.f,exports.f,unboundexports.f,unbound.f+sym,exportmodule.f)
     else 
          firstpass( modname.f, uses.f,defines.f+sym,if  input_1="Function" _1 then exports.f+sym else exports.f,unboundexports.f,unbound.f,exportmodule.f)
  else if input_1 in "module Module"  then
      firstpass(  mytype(if length.input > 2  then  ("T"+input_2) else [input_2]),uses.f,defines.f,exports.f,unboundexports.f,unbound.f,
       input_2 in exported)
  else f
  
 
use set.firstpass

use set.mytype



Function deepcopybody( knownsymbols:symbolset, type:mytype)seq.word 
 if abstracttype.type in "encoding int word"  
  then"PARAM 1"
  else if abstracttype.type ="seq"_1 
  then let typepara = parameter.type 
   let dc = mangle(merge("deepcopy:"+print.type),mytype."internal",empty:seq.mytype)
   let pseqidx = mangle("+"_1,mytype(towords.typepara+"pseq"),[ mytype."T pseq", mytype."int"])  
   let cat = mangle("+"_1,type ,[mytype."T seq", mytype."T seq"]) 
   let blockit = mangle("blockit"_1, mytype(towords.typepara+"blockseq"), [ mytype."T seq"])
   {"LIT 0 LIT 0 RECORD 2 PARAM 1 FREF"+dc +"FREF"+ cat +"FREF"+ pseqidx +"APPLY 5"+ blockit } 
  else 
     let name=mangle(merge(" typedesc:"+print.type),mytype."internal",empty:seq.mytype)
     let a = knownsymbols_name
    subfld(src.a,1,0,0)
  
  function subfld(desc:seq.word, i:int ,fldno:int,starttype:int) seq.word
  if i > length.desc then 
        "RECORD"+ toword.fldno
       else if desc_i="."_1 then
         subfld(desc,i+2,fldno,starttype)
        else if desc_i ="seq"_1 then
          subfld(desc,i+1,fldno,i)
        else if starttype > 0 then
           "PARAM 1 LIT"+toword(fldno)+"IDXUC" +mangle(merge("deepcopy:"+subseq(desc,starttype,i-1)),mytype."internal",empty:seq.mytype)
           +subfld(desc,i+1,fldno+1,0)
        else 
      "PARAM 1 LIT"+toword(fldno)+"IDXUC" 
      +subfld(desc,i+1,fldno+1,0)
   

  



 
 use seq.ipair.tree.seq.word