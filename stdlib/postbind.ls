#!/usr/local/bin/tau

run mylib test10


 
module postbind

use pass1

use stdlib

use set.symbol

use seq.symbol

use seq.myinternaltype

use symbol

use seq.mytype

/function print3(s:symbol)  seq.word  if (zcode.s)_1=s then print.s else print.s+ "->" +print.(zcode.s)_1
+if length.zcode.s=1 then "NO CODE" else "" 
   
Function postbind(alltypes:seq.myinternaltype,dict:set.symbol,working:set.symbol
,toprocess: seq.symbol,i:int,result:program,sourceX:program,tempX:program) program
// assert true report @(seperator."&br",print3,"",toseq.toset.tempX) //
  if i > length.toprocess then   result
  else
        let s=toprocess_i
        let w=working+toprocess_i
        if  cardinality.w=cardinality.working then 
          postbind(alltypes, dict, w,toprocess,i+1,result, sourceX,tempX )
        else 
           let lr1=lookupcode(sourceX,s)
          assert isdefined.lr1 report "postbind:expected to be defined:"+print.s
           let modname=mytype.module.s
          if // isbuiltin //  modname=mytype."builtin"   then 
             postbind(alltypes, dict, w,toprocess,i+1,result,sourceX ,tempX )
          else 
           let r=postbind3(alltypes, dict,  code.lr1, 1, empty:seq.symbol,parameter.modname,print.s,empty:set.symbol
           , sourceX,tempX )
            postbind(alltypes, dict,w,toseq(calls.r-w)+subseq(toprocess,i+1,length.toprocess),1,
           if  length.toprocess=1 &and toprocess_1=newsymbol("Wroot",mytype."W",empty:seq.mytype,mytype."int")    
           then result else  map(result,s,code.r), sourceX.r,tempX )
 
     
type resultpb is record calls:set.symbol,code:seq.symbol,sourceX:program

 function tokind(alltypes:seq.myinternaltype,x:mytype,p:mytype) mytype
       mytype.[parakind(alltypes,replaceT(x,p))]
 
function postbind3(alltypes:seq.myinternaltype,dict:set.symbol,code:seq.symbol,i:int,result:seq.symbol, 
  modpara:mytype,org:seq.word,calls:set.symbol,sourceX:program,tempX:program)resultpb
 if i > length.code then  
 resultpb(calls ,  result,sourceX)
 else 
   let x=code_i
   let isfref=isFref.x
   let sym= basesym.x
   if  isrecord.sym   then
      let a=Record.@(+,tokind(alltypes,modpara),empty:seq.mytype,paratypes.sym)
         postbind3(alltypes,dict,code,i+1,result+ if isfref  then  Fref.a else   a ,modpara,org, calls, sourceX ,tempX)
   else if isblock.sym then 
      let a=Block(tokind(alltypes,modpara,resulttype.sym),nopara.sym)
      postbind3(alltypes,dict,code,i+1,result+ if isfref  then  Fref.a else   a ,modpara,org, calls, sourceX ,tempX)
   else if isapply.sym then
        let newapply= Apply(nopara.sym,   [parakind(alltypes,replaceT(modpara,parameter.modname.sym))],
   [parakind(alltypes,replaceT(modpara,resulttype.sym))])
          postbind3(alltypes,dict,code,i+1,result+newapply,modpara,org, calls, sourceX ,tempX)     
   else  if  isnocall.sym  then
      postbind3(alltypes,dict,code,i+1,result+ code_i,modpara,org, calls, sourceX ,tempX)
   else
     let lr1=lookupcode(sourceX,sym)
      let newsym = if isdefined.lr1 then sym else replaceTsymbol(modpara, sym)
      let xx4 = if newsym=sym then lr1 else // check to see if template already has been processed // lookupcode(sourceX, newsym)
       if isdefined.xx4 then
         if not.isfref &and  ("VERYSIMPLE"_1  in options.code.xx4) then 
            let p2= subseq(code.xx4,nopara.newsym+1,length.code.xx4-2) 
              postbind3( alltypes,dict,code, i+1, result+p2 , modpara,org,calls   , sourceX,tempX  )  
         else       
        let p2=if isfref then Fref.target.xx4 else target.xx4
        postbind3(alltypes, dict, code, i + 1, result + p2, modpara, org, calls + target.xx4, sourceX, tempX)
       else if abstracttype.modname.sym in "builtin"then
       let codeforbuiltin = codeforbuiltin(alltypes, newsym, sym, org)
         postbind3(alltypes, dict, code, i + 1, result + if isfref then Fref.newsym else newsym, modpara, org, calls + newsym, map(sourceX, newsym, codeforbuiltin), tempX)
       else handletemplates(alltypes, dict, code, i, result, isfref, newsym, modpara, org, calls, sourceX, tempX)
       
    
  
    
 function handletemplates(alltypes:seq.myinternaltype, dict:set.symbol, code:seq.symbol, i:int, result:seq.symbol, isfref:boolean, oldsym:symbol, modpara:mytype, org:seq.word, calls:set.symbol
, sourceX:program, tempX:program)resultpb
   assert not(last.module.oldsym = "builtin"_1)report"ISb" + print.oldsym
   assert not("T"_1 in fsig.oldsym) ∧ not((module.oldsym)_1 = "T"_1)  ∧ not((returntype.oldsym)_1 = "T"_1)report"has T" + print.oldsym
   let fx = lookupcode(tempX, oldsym)
   if isdefined.fx then
   let newsource = if isdefined.lookupcode(sourceX, oldsym)then sourceX else map(sourceX, oldsym, code.fx)
     postbind3(alltypes, dict, code, i + 1, result + if isfref then Fref.oldsym else oldsym, modpara, org, calls + oldsym, newsource, tempX)
   else
      let k = lookup(dict, name.oldsym, paratypes.oldsym)
      assert cardinality.k = 1 report"Cannot find template for" + name.oldsym+"("+@(seperator.",",print,"",paratypes.oldsym)+")" + "while processing"+org
      assert not(oldsym = k_1)report"ERR12" + print.oldsym + print.k_1
      let dd = lookupcode(sourceX, k_1)
       if isdefined.dd then
       postbind3(alltypes, dict, code, i + 1, result + if isfref then Fref.k_1 else k_1, modpara, org, calls + k_1, sourceX, tempX)
       else
        // handles parameterized unbound cases like ?(int arc, int arc)graph.int"//
        handletemplates(alltypes, dict, code, i, result, isfref, k_1, modpara, org, calls, sourceX, tempX)
    
           
          
 function codeforbuiltin(alltypes:seq.myinternaltype,newsym:symbol ,oldsym:symbol,org:seq.word ) seq.symbol                          
           let newmodpara = parameter.modname.newsym 
             if     fsig.oldsym="sizeoftype:T"   then
             let typdesc=lookuptype(alltypes,newmodpara)
            assert  not.isempty.typdesc  report"can not find type sizeof" + print.newmodpara + org
            [Lit.size.typdesc_1  ]
            else if fsig.oldsym=" callidx(T seq, int)"   then
               let typedesc=lookuptype(alltypes, newmodpara) 
              assert not.isempty.typedesc report "type not found"+print.newmodpara
               [Local.1,Local.2,Callidx.kind.typedesc_1] 
            else  if   fsig.oldsym="packed(T seq)"     then
               let typdesc=lookuptype(alltypes,newmodpara)
               assert  not.isempty.typdesc  report"can not find type packed" + print.newmodpara  + org
               packedcode( typdesc_1) 
            else if fsig.oldsym="memcpy(int, int, int seq, int, int seq)"   then  memcpycode.newsym 
            else if  (fsig.oldsym)_1  = "deepcopy"_1   then  
                assert length.towords.parameter.modname.newsym > 0 report "DEEP"+print.newsym
                 definedeepcopy(alltypes, parameter.modname.newsym,org)          
            else  if  fsig.oldsym="assert(word seq)" then
               let typdesc=lookuptype(alltypes,resulttype.newsym)
               assert  not.isempty.typdesc  report"can not find type  " + print.newsym
               let kind=kind.typdesc_1
               let codesym=if kind="int"_1 then symbol("assert (word seq)","builtin","int")
                 else if kind="real"_1 then symbol("assert:real(word seq)","builtin","real")
                 else symbol("assert:ptr(word seq)","builtin","ptr")
                   [Local.1,codesym]     
           else if  fsig.oldsym="empty:seq.T"  then    
             Emptyseq+[  Words."VERYSIMPLE",Optionsym ] 
           else if fsig.oldsym= " getseqtype(T seq) " then  
           [Local.1,Lit.0,Idx."int"_1,Words."VERYSIMPLE",Optionsym ] 
           else if fsig.oldsym="aborted(T process) " then 
            [Local.1,symbol("aborted(T process)","builtin","boolean")] 
            else if fsig.oldsym="primitiveadd(T encodingpair)" then     
                let addefunc= newsymbol("add", mytype(towords.newmodpara + "encoding"),[ mytype(towords.newmodpara +" encodingstate"), mytype(towords.newmodpara+"  encodingpair")]
                   ,mytype(towords.newmodpara +" encodingstate"))
                let add2=newsymbol("addencoding",mytype."builtin",[mytype("int"),mytype("int seq"),mytype."int"],mytype."int")
                encodenocode(newmodpara)+[Local.1,Fref.addefunc,add2,Words."NOINLINE STATE",Optionsym]
            else    assert    fsig.oldsym= "getinstance:encodingstate.T" report "next expecting"+print.oldsym
              let get=symbol("getinstance(int)", "builtin","ptr")
              encodenocode(newmodpara)+[get,Words."NOINLINE STATE",Optionsym]  
           
   function encodenocode(typ:mytype) seq.symbol
       let gl=symbol("global"+  print.typ ,"builtin",("int seq"))
     let setfld=symbol("setfld(T seq, int, int)","builtin","int")
     let encodenosym=newsymbol ("encodingno",mytype("assignencodingnumber"),[mytype."word seq"],mytype."int")
     let IDXI=Idx."int"_1
       if typ=mytype."typename" then  
           [gl,Lit.0,Lit2,setfld,Define."xx",gl,Lit.0,IDXI] 
          else if typ=mytype."char seq " then 
                [gl,Lit.0,Lit.1,setfld,Define."xx",gl,Lit.0,IDXI] 
          else 
           [gl,Lit.0,IDXI, Lit.0,EqOp,Lit.3,Lit.2,Br
           ,gl,Lit.0,IDXI,Exit,  
           gl,Lit.0,Words.towords.typ,encodenosym,setfld,Define."xx",gl,Lit.0,IDXI ,Exit,Block(mytype."int",3)]   


function packedcode(typdesc:myinternaltype) seq.symbol
  let ds=size.typdesc 
  let IDXI=Idx."int"_1
if ds=1 then
[Local.1,  Lit.1,IDXI, Lit.0 ,Local.1,  Lit.1,IDXI
,symbol("allocateseq:seq.T(int, int, int)","builtin","ptr")
,Define."newseq" 
,Local."newseq"_1  
,Lit.2 
,Local.1
, Fref.symbol(" identity( int )","int seq" ,"int") 
, Fref.symbol("setfld(T seq, int, int)","builtin","int")
, Fref.symbol("_( int pseq, int)","int seq" ,"int") 
,Apply(6,"int","int")
,Define."d" 
,Local."newseq"_1]
else 
   [Lit.ds, Local.1,  Lit.1,IDXI,symbol("*(int, int)","builtin","int") 
    , // Fref.symbol("_( int packedseq, int)",typeT+"process",typeT)  // Lit.ds
    , Local.1,  Lit.1,IDXI
    , symbol( "allocateseq:seq.T(int, int, int)","builtin","ptr")  
    , Define."newseq" 
    , Lit.0
    , Lit.ds
    , Local."newseq"_1
    , Lit.2 
 , Local.1 
 , Fref.symbol(" identity( int seq )","int seq" ,"int seq")    
 , Fref.symbol("memcpy(int, int, int seq, int, int   seq)" , "int builtin" ,"int")
 , Fref.symbol("_( int pseq, int)","int seq" ,"int") 
 ,Apply(8,"ptr","int")
,Define."d" 
,Local."newseq"_1]
             
 function memcpycode(sym:symbol) seq.symbol
  assert module.sym="int builtin" report "not expecting module other than process.int"+print.sym
// function memcpy(i:int,memsize:int, s:seq.T,idx:int, fromaddress:seq.T) int 
if memsize=0 then idx else
   memcpy(i+1,memsize-1,s,setfld(s,idx,getval(fromaddress,i)),fromaddress) //
let i=1 let memsize=2 let s= 3 let idx=4 let fromaddress=5
  [Local.memsize, Lit.0, EqOp, Lit.2, Lit.3, Br  
  ,Local.idx, Exit
,Local.i, Lit.1 ,PlusOp ,Local.memsize, Lit.1,
symbol("-(int,int)" ,"builtin","int"),Local.s ,Local.s ,Local.idx ,Local.fromaddress ,Local.i,Idx."ptr"_1,
 symbol( "setfld(T seq, int, ptr)","builtin","int") ,
 Local.fromaddress,  sym,Exit 
,Block(mytype."int",3) ]   

function definedeepcopy(alltypes:seq.myinternaltype, type:mytype ,org:seq.word) seq.symbol
   if abstracttype.type in "encoding int word"then [Local.1]
 else
  if abstracttype.type = "seq"_1 then
  let kind=parakind(alltypes,parameter.type)
  let typepara = if kind in "int real" then mytype.[kind] else parameter.type
  let seqtype=mytype(towords.typepara + "seq")
    let dc =  deepcopysym.typepara 
   let pseqidx =  pseqidxsym.typepara
   let cat =  newsymbol("+", seqtype,  [ seqtype,typepara],seqtype)
   let blockittype =  if abstracttype.typepara="seq"_1 then  "int seq" else towords.typepara
   let blockit = newsymbol("blockit",mytype(blockittype+"blockseq"),  [ mytype(blockittype+"seq")],mytype(blockittype+"seq"))
    Emptyseq+[  Local.1, Fref.dc ,Fref.cat, Fref.pseqidx,Apply(5,
    if kind="seq"_1 then "ptr" else [kind],"ptr"), blockit]
  else
     let typedesc=lookuptype(alltypes, type)
    assert  not.isempty.typedesc  report"can not find type deepcopy" + print.type +org
      let y=subfld(subflds.typedesc_1,1,empty:seq.symbol)
    if size.typedesc_1  = 1 then
     // only one element in record so type is not represent by actual record //[Local.1]
      + subseq(y, 4, length.y - 1)
     else
      assert size.typedesc_1  ≠ 1 report"Err99a"+print.typedesc_1
       y
 
function subfld(flds:seq.mytype,fldno:int,result:seq.symbol) seq.symbol
  if fldno > length.flds then result+[Record.flds]
  else let fldtype=flds_fldno
  let t=if abstracttype.fldtype in "encoding int word"then "int"
    else if abstracttype.fldtype in " real"then "real"   
    else
    assert abstracttype.fldtype = "seq"_1 report"ERR99" + print.fldtype
     "ptr"
     subfld(flds,fldno+1,result+[ Local.1,Lit.(fldno-1),Idx.t_1,deepcopysym.fldtype]) 
 
 