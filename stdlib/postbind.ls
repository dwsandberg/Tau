#!/usr/local/bin/tau

run mylib test10


 
module postbind

use pass1

use stdlib

use set.symbol

use seq.symbol

use symbol

use seq.mytype

/function print3(s:symbol)  seq.word  if (zcode.s)_1=s then print.s else print.s+ "->" +print.(zcode.s)_1
+if length.zcode.s=1 then "NO CODE" else "" 
   
Function postbind(alltypes:typedict,dict:set.symbol,working:set.symbol
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
           let r=postbind3( alltypes, dict,  code.lr1, 1, empty:seq.symbol,parameter.modname,print.s,empty:set.symbol
           , sourceX,tempX )
            postbind(alltypes, dict,w,toseq(calls.r-w)+subseq(toprocess,i+1,length.toprocess),1,
           if  length.toprocess=1 &and toprocess_1=newsymbol("Wroot",mytype."W",empty:seq.mytype,mytype."int")    
           then result else  map(result,s,code.r), sourceX.r,tempX )
 
     
type resultpb is record calls:set.symbol,code:seq.symbol,sourceX:program

 function tokind(alltypes:typedict,x:mytype,p:mytype) mytype
       mytype.[kind.gettypeinfo( alltypes,replaceT(x,p))]
 
function postbind3(alltypes:typedict,dict:set.symbol,code:seq.symbol,i:int,result:seq.symbol, 
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
        let newapply= Apply(nopara.sym,   [kind.gettypeinfo(alltypes,replaceT(modpara,parameter.modname.sym))],
   [kind.gettypeinfo(alltypes,replaceT(modpara,resulttype.sym))])
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
        if fsig.sym="offsets" then
             let fldtypdesc=gettypeinfo(alltypes,replaceT(modpara,resulttype.sym))
             let fldkind=if kind.fldtypdesc ="seq"_1 then "ptr"_1 else kind.fldtypdesc  
             let a1=break(","_1,replaceT(towords.modpara,towords.parameter.modname.sym),2)
             let a4=@(+,bbb.alltypes,toint.(module.sym)_1,a1)
             let p2=if size.fldtypdesc = 1 then
                      [Lit.a4,Idx.fldkind]
                     else 
                     [ Lit.a4,Lit.size.fldtypdesc  ,symbol("cast(T seq,int,int)","builtin","ptr") ]
               postbind3( alltypes,dict,code, i+1, result+p2 , modpara,org,calls   , sourceX,tempX  )       
         else if (fsig.sym)_1 in "build" then
             let a=if length.towords.modpara > 0 then replaceT(towords.modpara,fsig.sym) else  fsig.sym
             let b=break(","_1,subseq(a,1,length.a-1),5)
             let c=@(+,gettypeinfo.alltypes,empty:seq.typeinfo,subseq(b,1,length.b))  
             assert length.b=length.c report "?"
             let p2= buildconstructor(if i=2 then [mytype."int"] else empty:seq.mytype,c)
         //    assert not( a_3 in "q") report "JKL"+toword.i+@(+,print,"",p2)+a //
                postbind3( alltypes,dict,code, i+1, result+p2 , modpara,org,calls   , sourceX,tempX  ) 
         else 
       let codeforbuiltin = codeforbuiltin(alltypes, newsym, sym, org)
         postbind3(alltypes, dict, code, i + 1, result + if isfref then Fref.newsym else newsym, modpara, org, calls + newsym, map(sourceX, newsym, codeforbuiltin), tempX)
       else handletemplates(alltypes, dict, code, i, result, isfref, newsym, modpara, org, calls, sourceX, tempX)
       
 
function bbb(alltypes:typedict,a:seq.word) int   size.gettypeinfo(alltypes,mytype.a) 
      
function gettypeinfo(alltypes:typedict,a:seq.word) typeinfo
                gettypeinfo(alltypes,mytype.a)
       
  use seq.typeinfo   
  
  
   function buildconstructor( addfld:seq.mytype, flds:seq.typeinfo) seq.symbol
buildconstructor(addfld,flds,empty:seq.mytype,1,1,0,empty:seq.symbol)

          
  function buildconstructor( addfld:seq.mytype, flds:seq.typeinfo,flatflds:seq.mytype,fldno:int,j:int,subfld:int,result:seq.symbol)
 seq.symbol
  // assert [fldno ,j ,subfld,length.flatflds] in [[ 1,1,0 ,0],[2,2,0,1],[2,3,1,4],[2,4,2,4],[3,5,0,4]]  report @(+,toword,"jkl",[fldno ,j ,subfld 
  ,length.flatflds,length.flds]) //
   if fldno > length.flds then result+ Record(addfld+flatflds) 
   else 
     let fldtype=flds_fldno
     let newflatflds=if j > length.flatflds then 
        let t=if kind.fldtype in "int real"then [mytype.[kind.fldtype]] 
            else if kind.fldtype ="seq"_1 then [mytype."ptr"] else subflds.fldtype 
        // assert length.t > 0 report "proglem"+print.fldtype //
        flatflds+t else flatflds
     let newresult=result+if size.fldtype=1 then  [Local.fldno] else 
     [Local.fldno ,Lit.subfld, Idx.abstracttype.newflatflds_j]
   if subfld  = size.fldtype-1 then
       buildconstructor(addfld,flds,newflatflds,fldno+1,j+1,0, newresult)
   else 
       buildconstructor(addfld,flds,newflatflds,fldno,j+1,subfld+1, newresult)
     
       
 function handletemplates(alltypes:typedict, dict:set.symbol, code:seq.symbol, i:int, result:seq.symbol, isfref:boolean, oldsym:symbol, modpara:mytype, org:seq.word, calls:set.symbol
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
    
           
 function codeforbuiltin(alltypes:typedict,newsym:symbol ,oldsym:symbol,org:seq.word ) seq.symbol                          
           let newmodpara = parameter.modname.newsym 
             if     fsig.oldsym="sizeoftype:T"   then
              [Lit.size.gettypeinfo(alltypes,newmodpara)  ]
            else if fsig.oldsym="processresult(T process)"   then
                [Local.1,Lit.2, Idx.kind.gettypeinfo(alltypes,newmodpara)] 
              else if fsig.oldsym=" callidx(T seq, int)"   then
                [Local.1,Local.2,Callidx.kind.gettypeinfo(alltypes,newmodpara)] 
            else  if   fsig.oldsym="packed(T seq)"     then
                 let ds=size.gettypeinfo(alltypes,newmodpara)
if ds=1 then
   [Local.1,symbol("packed1(int seq)","assignencodingnumber","int seq")]
else 
 [Lit.ds,Local.1,symbol("packed(int,int seq seq)","assignencodingnumber","int seq")]
            else if  (fsig.oldsym)_1  = "deepcopy"_1   then  
                assert length.towords.parameter.modname.newsym > 0 report "DEEP"+print.newsym
                 definedeepcopy(alltypes, parameter.modname.newsym,org)          
            else  if  fsig.oldsym="assert(word seq)" then
                let kind=kind.gettypeinfo(alltypes,resulttype.newsym)
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
            else assert    fsig.oldsym= "getinstance:encodingstate.T" report "not expecting"      + print.oldsym
              let get=symbol("getinstance(int)", "builtin","ptr")
              encodenocode(newmodpara)+[get,Words."NOINLINE STATE",Optionsym]  
              
              use mangle
           
   function encodenocode(typ:mytype) seq.symbol
       let gl=symbol("global"+  print.typ ,"builtin","int seq")
     let setfld=symbol("setfld(int seq, int, int)","builtin","int")
     let encodenosym=newsymbol ("encodingno",mytype("assignencodingnumber"),[mytype."word seq"],mytype."int")
     let IDXI=Idx."int"_1
       if typ=mytype."typename" then  
           [gl,Lit.0,Lit.2,setfld,Define."xx",gl,Lit.0,IDXI] 
          else if typ=mytype."char seq " then 
                [gl,Lit.0,Lit.1,setfld,Define."xx",gl,Lit.0,IDXI] 
          else 
           [gl,Lit.0,IDXI, Lit.0,EqOp,Lit.3,Lit.2,Br
           ,gl,Lit.0,IDXI,Exit,  
           gl,Lit.0,Words.towords.typ,encodenosym,setfld,Define."xx",gl,Lit.0,IDXI ,Exit,Block(mytype."int",3)]   


             
 
function definedeepcopy(alltypes:typedict, type:mytype ,org:seq.word) seq.symbol
 if abstracttype.type in "encoding int word"then [Local.1]
 else if abstracttype.type = "seq"_1 then
     let ds=size.gettypeinfo(alltypes,type)
     let kind=kind.gettypeinfo(alltypes,parameter.type)
     let typepara = if kind in "int real" then mytype.[kind] else parameter.type
     let seqtype=mytype(towords.typepara + "seq")
     let dc =  deepcopysym.typepara 
     let pseqidx =  pseqidxsym.typepara
     let cat =  newsymbol("+", seqtype,  [ seqtype,typepara],seqtype)
        Emptyseq+[  Local.1, Fref.dc ,Fref.cat, Fref.pseqidx,Apply(5, [kind],"ptr")]
     + if ds=1 then
          [symbol("packed1(int seq)","assignencodingnumber","int seq")]
        else 
          [Local.1,Lit.ds,symbol("packed(int seq seq,ds)","assignencodingnumber","int seq")]
 else
    let typedesc=gettypeinfo(alltypes, type)
    let y=subfld(subflds.typedesc ,1,empty:seq.symbol)
    if size.typedesc   = 1 then
      // only one element in record so type is not represent by actual record //
      [Local.1]  + subseq(y, 4, length.y - 1)
     else
      assert size.typedesc   ≠ 1 report"Err99a"+print.type
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
 
 