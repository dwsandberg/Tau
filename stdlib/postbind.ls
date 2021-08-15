module postbind

use standard

use symbol

use program
 
use seq.symbol

use set.symbol

use seq.seq.symbol

use set.symdef

use seq.symdef

use seq.mytype

use seq.seq.mytype

use encoding.symbol

use seq.encodingpair.symbol

use intdict.seq.symbol

use otherseq.mytype

use otherseq.word

use seq.findabstractresult 

use passsymbol

use seq.set.symdef
    
function verysimpleinline(sd:symdef) boolean
 let nopara=nopara.sym.sd
 for acc=true,idx=1,sym=code.sd  while acc do
   if idx /le nopara then
     next(sym=Local.idx,idx+1)
   else 
   if islocal.sym then
     next(false,idx+1) 
   else next(inmodule(sym,"$int") /or inmodule(sym ,"builtin")  /and name.sym="fld"_1
   /or  inmodule(sym,"standard") /and name.sym /nin "randomint" 
   /or inmodule(sym,"bits") /or inmodule(sym,"internal") /and name.sym /in "getseqlength"
   /or inmodule(sym,"real")
   ,idx+1) 
  /for(acc)
  
  function vinline(toprocess:set.symdef,orginline:set.symdef) seq.set.symdef
  let tmp=for   other=empty:set.symdef,    inline=orginline ,sd=toseq.toprocess do 
   let z= for acc=empty:seq.symbol,     sym=code.sd do
      if not.isempty.acc /and last.acc=PreFref then acc+sym else
      let f= findelement(  symdef(sym,empty:seq.symbol),inline)
      if  isempty.f then acc+sym else acc+(  code.(f_1) << nopara.sym)
    /for(symdef(sym.sd,acc))
   if verysimpleinline.z then next(other,inline+z) else next(other+z,inline )
 /for([other,inline])
 if cardinality.orginline=cardinality.tmp_2 then tmp
 else vinline(tmp_1,tmp_2)




type postbindresult  is typedict:type2dict ,prg:program 

Export typedict(postbindresult) type2dict

Export prg(postbindresult) program


type  mapsymbolused is  modname:modref,syms:set.symbol

function ?(a:mapsymbolused,b:mapsymbolused) ordering  modname.a ? modname.b 

use set.mapsymbolused

function add(b:set.mapsymbolused,sd:symdef) set.mapsymbolused
  let new= for  acc=empty:set.symbol , sym=code.sd do
    if not.isunbound.sym /and isabstract.module.sym /and  name.module.sym /nin "$for $loopblock $sequence builtin" then  
     acc+sym  else acc
    /for( acc)
   if isempty.new then b
 else
 let m1=mapsymbolused(module.sym.sd,new)
 let f=   findelement(m1,b)
 if isempty.f then 
   b+m1
 else 
   replace(b,mapsymbolused(module.sym.sd,syms.f_1 /cup new))
   
 
   
   
      function print (a:set.mapsymbolused) seq.word
      for acc="sym used", e=toseq.a do acc+print.modname.e+  print.toseq.syms.e +   EOL /for(acc) 
      
  
Function postbind( t5:prg6, roots:seq.symbol, theprg:program, 
templates:program,compiled:set.symbol , typedict1:type2dict
)postbindresult
 let root = symbol(moduleref."W","Wroot", typeint)
   let discard=for acc=0 ,r=roots do let discard2=encode.r 0 /for(0)
  usedsyms(theprg ,0,empty:seq.symdef
 ,templates 
 ,compiled,typedict1 )
 
 assert false report 
  for txt="DEBUG",   d=encoding:seq.encodingpair.debug do
   txt+data.data.d +EOL /for(txt)
 j


 function usedsyms(source:program ,last:int,result:seq.symdef
 , templates:program
  ,compiled:set.symbol,typedict1:type2dict ) postbindresult
     let a=  encoding:seq.encodingpair.symbol 
     if length.a=last   then postbindresult(typedict1,program.asset.result )
    else 
     for  acc=result, newtypedict=typedict1 , p=subseq(a,last+1,length.a) do
       let sym=data.p
       if isspecial.sym /or isconst.sym 
             /or name.module.sym /in "builtin internal $for $global" 
              then next(acc,newtypedict)
       else
          let newdict2=addtype(newtypedict,resulttype.sym)
          let lr1 = getCode(source, sym)                  
          let sd=if (not.isempty.lr1 /or sym /in compiled) then 
                 symdef(sym,lr1) 
            else  if istype.sym then
              symdef(sym,deepcopybody(resulttype.sym,newdict2 )) 
            else  if not.isunbound.sym then sub5(sym,compiled ,templates )
            else
              let k2=      lookupbysig(data.source,sym)
                if isempty.k2 then sub5(sym,compiled ,templates )
                  else    
                     let txt0=print.sym
                   let pick=  if cardinality.k2 = 1 then  k2
                    else 
                       let n=k2_1
                       if name.n="?"_1 /and name.module.n="graph"_1 /and
                         cardinality.k2=2 then  asset.[k2_2]
                     else 
                      for pick=empty:set.symbol  ,sy=toseq.k2 do 
                      if print.sy /in ["otherseq.seq.word:?(seq.word, seq.word)ordering",
                   "standard:*(int, int)int","standard:+(int, int)int"
                   ,"standard:=(int, int)boolean"
                   ,"standard:?(int, int)ordering"
                   ,"symbol:?(symbol, symbol) ordering "
                   ,"words:?(word, word)ordering"
                   ,"standard:=(char, char)boolean"
                   ,"checkdata2:?(rec, rec)ordering"
                   ,"point:?(point, point)ordering"
                   ,"words:?(alphaword, alphaword)ordering"
                   ,"words:=(word, word)boolean"
                   ,"seq.word:=(seq.word, seq.word)boolean"
                   ,"genLR1:?(dottedrule, dottedrule)ordering"
                   ,"genLR1:?(action, action)ordering"
                   ,"genLR1:?(action2, action2)ordering"
                   ,"genLR1:=(dottedrule, dottedrule)boolean"
                   ,"checkdata2:?(rollup, rollup)ordering"
                   ,"mytype:=(mytype, mytype)boolean"
                    ,"mytype:?(mytype, mytype)ordering"
                   ,"llvmconstants:=(instop, instop)boolean"
                   ,"llvmconstants:=(constop, constop)boolean"
                   ,"profile:?2(parc, parc)ordering"] then
                          pick+sy else pick
                  /for(pick)   
                    assert cardinality.pick=1 report  "postbind problem"+print.toseq.k2+
                         "pick:"+print.toseq.pick     
                   sub5(pick_1,compiled ,templates )
               let  newdict3=addtypes(newdict2, asset(code.sd+sym.sd)) 
            next(acc+symdef(sym ,postbind(sd,newdict3,  compiled)   ),newdict3)   
         /for(usedsyms(source, length.a,acc
         ,templates 
         ,compiled,typedict1  ))  
         

         
         function sub5(sym2:symbol,compiled:set.symbol,templates:program) symdef   
              if   issimple.module.sym2 /or sym2 /in compiled then 
                    for paras=empty:seq.symbol,i=arithseq(nopara.sym2,1,1) do paras+Local.i 
                    /for (symdef(sym2,  paras+sym2))
               else  
                 let gx=findabstract2(templates,sym2)
                   assert length.gx = 1 report"Cannot find template for X"  +
                    print.length.gx+ print.sym2  
                  for newcode=empty:seq.symbol,sym4 = code.sd.gx_1 do  
                         assert { print.sym.sd.gx_1 /ne "set.T:+(set.T,  T)set.T"
                         /or length.print.modpara.gx_1=1 } not.isunbound.sym.sd.gx_1 report 
                        "HHH"+print.modpara.gx_1+print.sym.sd.gx_1          +print.sym4  
                      newcode+replaceTsymbol(modpara.gx_1, sym4) 
                 /for(symdef(  sym2 ,    newcode))  
            


Function postbind(sd:symdef,typedict:type2dict,   compiled:set.symbol) seq.symbol
let modpara = para.module.sym.sd
 let pdict = for pmap = empty:intdict.seq.symbol, parano = 1, e = constantseq(10000, 1)while parano ≤ nopara.sym.sd do 
               next(add(pmap, parano, [ Local.parano]), parano + 1)
            /for(pmap)
for nextvar = nopara.sym.sd + 1, map = pdict,result = empty:seq.symbol ,  symx = code.sd do
         let sym = replaceTsymbol(modpara, symx)
     if name.module.sym ∈ "$define"then
      next(nextvar + 1, replace(map, value.sym, [ Local.nextvar]),   result + Define.nextvar)
     else if name.module.sym ∈ "$local"then
       let t = lookup(map, value.sym)
        next(nextvar, map,   result + t_1)  
     else  if isspecial.sym then
     let p2 = if isSequence.sym then Sequence(parameter.basetype(   resulttype.sym,typedict), nopara.sym)
            else if isstart.sym then Start.basetype(  resulttype.sym,typedict)
          else sym
       next(nextvar,map,result + p2 )
    else if isconst.sym ∨ inmodule(sym,"$global") ∨ inmodule(sym,"internal") /or sym=PreFref /or sym= Optionsym then 
       next(nextvar,map,result + sym)
    else if inmodule(sym,"$for")then next(nextvar,map,result + sym )
    else 
       if not.inmodule(sym,"builtin")then
            let t4= findelement(sym,compiled) 
            next(nextvar,map,result+if isempty.t4 then sym else t4_1 )  
       else 
         if  name.sym ∈ "primitiveadd" then
        let encodingtype = typeref."encoding encoding. "
       let encodingstatetype = typeref."encodingstate encoding. "
       let encodingpairtype = typeref."encodingpair encoding. "
       let addefunc = symbol(moduleref("encoding", para.module.sym),"add", [ addabstract(encodingstatetype, para.module.sym), addabstract(encodingpairtype, para.module.sym)], addabstract(encodingstatetype, para.module.sym))
       let add2 = symbol(internalmod,"addencoding", [ typeint, typeptr, typeint, typeint], typeint)
       let dc = deepcopySym(  addabstract(encodingpairtype, para.module.sym))
         next(nextvar+1,map,result+[ PreFref,addefunc, PreFref,dc, add2] )
      else if name.sym ∈ "getinstance"then
          let get = symbol(internalmod,"getinstance", typeint, typeptr)
            next(nextvar+2,map,result + encodenocode(para.module.sym,nextvar) +   get  )
        else  next(nextvar,map   
      ,    if name.sym ∈ "pushflds" then
            if iscoretype.para.module.sym then result
            else
             let t = flatflds(typedict,para.module.sym)
             if isempty.t /or typeT ∈ t  then 
                    result+sym
             else if length.t=1  then result
             else 
              for newresult=result >> 1 , idx=0, x=t do
                 next(newresult+ [last.result,Lit.idx,Getfld.x],idx+1)
              /for(newresult) 
      else  if name.sym ∈ "buildrecord" then
        let t = flatflds(typedict,para.module.sym)
        result+if isempty.t /or typeT ∈ t then sym  else  Record.t
    else  if name.sym ∈  "bitcast"  then
     let a = coretype(first.paratypes.sym, typedict)
      let b = coretype(resulttype.sym, typedict)
      if a = b then result else   result + symbol(internalmod,"bitcast", a, b)
    else result+  if name.sym ∈ "processresult"then
            [ Lit.2 , Getfld.coretype( para.module.sym,typedict )]
   else [ if name.sym ∈ "typesize"then
       let typ=para.module.sym
          if typ = typeint ∨ typ = typereal ∨ typ = typeptr /or isseq.typ then Lit.1
              else      
               let t = flatflds(typedict,typ)  
        if isempty.t /or typeT ∈ t then sym else Lit.length.t
  else     if name.sym ∈ "length"then  GetSeqLength
else if name.sym ∈ "packed"then 
 let typ=seqof.coretype(para.module.sym, typedict)
          symbol(moduleref( "tausupport"),"blockIt", typ,typ)
     else if name.sym ∈ "aborted"then   symbol(internalmod,"aborted", typeptr, typeboolean)
 else if name.sym ∈ "assert "  then
      abortsymbol.coretype(para.module.sym, typedict)
        else if name.sym ∈ "_"then
     let seqtype = basetype(first.paratypes.sym,typedict)
          symbol(internalmod,"indexseq45", seqtype, typeint,  parameter.seqtype )
       else if name.sym ∈ "getseqtype"then   GetSeqType
      else if name.sym ∈ "set"then
         setSym.coretype(para.module.sym, typedict)
      else if name.sym = "forexp"_1 then  
  let paras = for acc = empty:seq.mytype, p = paratypes.sym do
  acc + if"$base"_1 ∈ print.p then p else  basetype( p,typedict)
 /for(acc)
  symbol(moduleref."builtin","forexp", paras, last.paras)
      else  if name.sym = "createthreadY"_1 then
        let paras = for paras = empty:seq.mytype, p = paratypes.sym do paras + coretype(p, typedict)/for(paras)
       let rt = processof.coretype( parameter.resulttype.sym , typedict)
        symbol(builtinmod.rt,"createthreadY", paras, typeptr)
       else if name.sym ∈ "fld getfld"then
            let typ=resulttype.sym  
            if iscoretype.typ then  Getfld.typ  
            else if isabstract.typ then sym 
            else
            let a=flatflds( typedict,typ)
            assert not.isempty.a report "cannot find type getfld" +print.typ
            if length.a > 1 then 
              symbol(internalmod,"GEP", seqof.typeptr, typeint, typeptr)
            else   Getfld.first.a  
        else if name.sym ∈ "empty" then Sequence(coretype(para.module.sym, typedict),0)
  else
        assert name.sym /in "offsets build" report "post bind"+print.sym
     sym
     ] )
   /for( let discard=for acc2=symbolref.EqOp, sym5=result  do  symbolref.sym5 /for(acc2) result)
       
 function iscoretype(typ:mytype) boolean
 typ =  typeint /or typ=typereal   /or typ=typeptr /or typ=typeboolean /or isseq.typ /or isencoding.typ

  function encodenocode(typ:mytype,varno:int)seq.symbol
  let gl = symbol4(moduleref."$global","global"_1, typ, empty:seq.mytype, seqof.typeint)
  let encodenosym = symbol(moduleref."tausupport","encodingno", seqof.typeword, typeint)
  if typ = typeref."typename tausupport. "then [  Lit.2 ]
  else if typ = seqof.typechar then  [   Lit.1 ]  
 else
  ifthenelse([ gl,Lit.0,Getfld.typeint,Define.varno,
     Local.varno , Lit.0, EqOp], [   gl, Words.print.typ, encodenosym, setSym.typeint, Define(varno+1), gl  
      ,Lit.0,Getfld.typeint],[ Local.varno],typeint)

use typedict


use mytype

      use seq.seq.mytype
      
        use set.symdef    



/function buildcode(acc:int, w:word)int
 acc * 2 + if w = first."real"then 1 else 0
 
 
{ base types are int real boolean ptr seq.int seq.real seq.boolean seq.ptr seq.byte seq.bit 
   seq.packed2 seq.packed3 seq.packed4 seq.packed5 seq.packed6 or $base.x where x is a integer}
            
Function  prescan2(   prg:program) program 
      for  acc=empty:set.symdef ,  p=tosymdefs.prg do
         for  result = empty:seq.symbol, sym = code.p do
          {if not.isempty.result ∧ last.result = PreFref then
               result >> 1+Fref.sym
           else} if  islocal.sym then
                 result +  Local.value.sym
           else if isdefine.sym then  result+Define.value.sym
           else result + sym
      /for(acc+symdef( sym.p,result))
      /for(program.acc)  
      
      Function  prescan2(   p:symdef) symdef
          for  result = empty:seq.symbol, sym = code.p do
            if  islocal.sym then
                 result +  Local.value.sym
           else if isdefine.sym then  result+Define.value.sym
           else result + sym
      /for( symdef( sym.p,result) )
      
 
 
use set.passsymbols

use seq.modref

use set.modref

          
   
       type debug is data:seq.word,k:int
    
 function    hash (d:debug) int hash.data.d
 
 function   assignencoding(l:seq.encodingpair.debug,debug) int length.l
 
 use seq.encodingpair.debug 
 
 
 
 use encoding.debug
 
 function =(a:debug,b:debug) boolean data.a=data.b
        
       