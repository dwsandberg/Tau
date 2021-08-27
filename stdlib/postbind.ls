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
   else next(isIntLit.sym   /or  isBuiltin.sym   /and name.sym="fld"_1
   /or    isInternal.sym /and name.sym /in "getseqlength "
   /or isRealLit.sym 
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




type postbindresult  is typedict:typedict ,prg:program 

Export typedict(postbindresult) typedict

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
templates:program , typedict1:typedict
)postbindresult
 let root = symbol(moduleref.". W","Wroot", typeint)
   let discard=for acc=0 ,r=roots do let discard2=encode.r 0 /for(0)
  usedsyms(theprg ,0,emptyprogram
 ,templates 
 ,typedict1 )
 
 assert false report 
  for txt="DEBUG",   d=encoding:seq.encodingpair.debug do
   txt+data.data.d +EOL /for(txt)
 j

  assert false report for txt=">>>",  sd=tosymdefs.theprg do
   for txt2=txt, sym=code.sd do
    if print.sym=
   "svggraph.seq.word:?(seq.word, seq.word)ordering" then txt2+print.sym.sd 
   else txt2 /for(txt2)
   /for(txt)   

use set.word




 function usedsyms(source:program ,last:int,result:program
 , templates:program
 ,typedict1:typedict ) postbindresult
     let aa=  encoding:seq.encodingpair.symbol 
     if length.aa=last   then postbindresult(typedict1,result )
    else 
     for  accZ=postbindresult(typedict1,result),   pp=subseq(aa,last+1,length.aa) do
       let symz=data.pp
       if isspecial.symz /or isconst.symz 
             /or name.module.symz /in "builtin  $for $global" 
              then accZ 
        else if isInternal.symz then
          let lr1 = getCode(source, symz) 
           if isempty.lr1 then accZ
           else 
            postbindresult(typedict.accZ,map(prg.accZ,symz,lr1)) 
       else
          let newdict2=addtype(typedict.accZ,resulttype.symz)
          let lr1 = getCode(source, symz)  
           let sd=if (not.isempty.lr1 /or  iscompiled(lr1,symz)) then 
                 symdef(symz,lr1) 
            else  if istype.symz then
              symdef(symz,deepcopybody(resulttype.symz,newdict2 )) 
            else  if not.isunbound.symz then 
             if   issimple.module.symz  then 
                    for paras=empty:seq.symbol,i=arithseq(nopara.symz,1,1) do paras+Local.i 
                    /for (symdef(symz,  paras+symz))
               else 
                sub5(symz  ,templates )
            else
                let k2=      lookupbysig(data.source,symz)
                if isempty.k2 then 
                  { assert length.print.module.symz > 3 report "XX"+print.symz}
                    if   issimple.module.symz  then 
                    for paras=empty:seq.symbol,i=arithseq(nopara.symz,1,1) do paras+Local.i 
                    /for (symdef(symz,  paras+symz))
               else 
                   sub5(symz,templates )
                  else    
                   assert cardinality.k2 = 1 report
                      "unbound problem"+print.symz 
                      let sym2=k2_1
                        if   issimple.module.sym2 /or
           iscompiled(getCode(source, sym2),sym2)  then
                    for paras=empty:seq.symbol,i=arithseq(nopara.sym2,1,1) do paras+Local.i 
                    /for (symdef(sym2,  paras+sym2))
               else     
                   sub5(k2_1,templates )
               let  newdict3=addtypes(newdict2, asset(code.sd+sym.sd)) 
               {------------}
              let modpara = para.module.sym.sd
 let pdict = for pmap = empty:intdict.seq.symbol, parano = 1, e = constantseq(10000, 1)while parano ≤ nopara.sym.sd do 
               next(add(pmap, parano, [ Local.parano]), parano + 1)
            /for(pmap)
  for cache=empty:set.symdef,nextvar = nopara.sym.sd + 1, map = pdict,result2 = empty:seq.symbol ,  symx = code.sd do
         let sym = replaceTsymbol(modpara, symx)
     if name.module.sym ∈ "$define"then
      next(cache,nextvar + 1, replace(map, value.sym, [ Local.nextvar]),   result2 + Define.nextvar)
     else if name.module.sym ∈ "$local"then
       let t = lookup(map, value.sym)
        next(cache,nextvar, map,   result2 + t_1)  
      else if isconst.sym  then 
       next(cache,nextvar,map,result2 + sym)
     else  if  name.sym ∈ "primitiveadd" /and isBuiltin.sym   then
        let encodingtype = typeref."encoding encoding stdlib "
       let encodingstatetype = typeref."encodingstate encoding stdlib "
       let encodingpairtype = typeref."encodingpair encoding stdlib "
       let addefunc = symbol(moduleref("stdlib encoding", para.module.sym),"add", [ addabstract(encodingstatetype, para.module.sym), addabstract(encodingpairtype, para.module.sym)], addabstract(encodingstatetype, para.module.sym))
       let add2 = symbol(internalmod,"addencoding", [ typeint, typeptr, typeint, typeint], typeint)
       let dc = deepcopySym(  addabstract(encodingpairtype, para.module.sym))
         next(cache,nextvar+1,map,result2+[ PreFref,addefunc, PreFref,dc, add2] )
      else if name.sym ∈ "getinstance" /and  isBuiltin.sym  then
          let get = symbol(internalmod,"getinstance", typeint, typeptr)
            next(cache,nextvar+2,map,result2 + encodenocode(para.module.sym,nextvar) +   get  )
     else  if name.sym ∈ "pushflds" /and  isBuiltin.sym  then
           next(cache,nextvar,map , if iscoretype.para.module.sym then result2
            else
             let t = flatflds(newdict3,para.module.sym)
             if isempty.t /or typeT ∈ t  then 
                    result2+sym
             else if length.t=1  then result2
             else 
              for newresult=result2 >> 1 , idx=0, x=t do
                 next(newresult+ [last.result2,Lit.idx,Getfld.x],idx+1)
              /for(newresult))
        else 
          let cacheValue=findelement(symdef(symx,empty:seq.symbol),cache)
          if not.isempty.cacheValue then
            next(cache,nextvar,map  , result2+ code.cacheValue_1)
          else 
            let newValue= test(symx,newdict3,modpara)
          next(cache+symdef(symx,newValue),nextvar,map  , result2+ newValue)
   /for( let discard=for acc2=symbolref.EqOp, sym5=result2  do  symbolref.sym5 /for(acc2) 
      postbindresult(newdict3,map(prg.accZ,symz,result2)) )
         /for(usedsyms(source, length.aa,prg.accZ
         ,templates 
         , typedict.accZ  ))  
 
 function test(symx:symbol,newdict3:typedict,modpara:mytype) seq.symbol 
  let sym = replaceTsymbol(modpara, symx) 
        if isspecial.sym then
       if isSequence.sym then [Sequence(parameter.basetype(   resulttype.sym,newdict3), nopara.sym)]
            else if isstart.sym then [Start.basetype(  resulttype.sym,newdict3)]
          else [sym] 
    else if isconst.sym ∨ isGlobal.sym ∨ isInternal.sym /or sym=PreFref /or sym= Optionsym then 
       [ sym]
    else if inModFor.sym /or not.isBuiltin.sym  then  [ sym ]
    else  if name.sym ∈ "buildrecord" then
        let t = flatflds(newdict3,para.module.sym)
        [if isempty.t /or typeT ∈ t then sym  else  Record.t]
    else  if name.sym ∈  "bitcast"  then
     let a = coretype(first.paratypes.sym, newdict3)
      let b = coretype(resulttype.sym, newdict3)
      if a = b then empty:seq.symbol else   [ symbol(internalmod,"bitcast", a, b)]
    else  if name.sym ∈ "processresult"then
            [ Lit.2 , Getfld.coretype( para.module.sym,newdict3 )]
   else [ if name.sym ∈ "typesize"then
       let typ=para.module.sym
          if typ = typeint ∨ typ = typereal ∨ typ = typeptr /or isseq.typ then Lit.1
              else      
               let t = flatflds(newdict3,typ)  
        if isempty.t /or typeT ∈ t then sym else Lit.length.t
  else     if name.sym ∈ "length"then  GetSeqLength
else if name.sym ∈ "packed"then 
 let typ=seqof.coretype(para.module.sym, newdict3)
          symbol(modTausupport ,"blockIt", typ,typ)
     else if name.sym ∈ "aborted"then   symbol(internalmod,"processisaborted", typeptr, typeboolean)
 else if name.sym ∈ "assert "  then
      abortsymbol.coretype(para.module.sym, newdict3)
        else if name.sym ∈ "_"then
     let seqtype = basetype(first.paratypes.sym,newdict3)
          symbol(internalmod,"indexseq45", seqtype, typeint,  parameter.seqtype )
       else if name.sym ∈ "getseqtype"then   GetSeqType
      else if name.sym ∈ "set"then
         setSym.coretype(para.module.sym, newdict3)
      else if name.sym = "forexp"_1 then  
  let paras = for acc = empty:seq.mytype, p = paratypes.sym do
  acc + if"$base"_1 ∈ print.p then p else  basetype( p,newdict3)
 /for(acc)
  symbol(moduleref.". builtin","forexp", paras, last.paras)
      else  if name.sym = "createthreadY"_1 then
        let paras = for paras = empty:seq.mytype, p = paratypes.sym do paras + coretype(p, newdict3)/for(paras)
       let rt = processof.coretype( parameter.resulttype.sym , newdict3)
        symbol(builtinmod.rt,"createthreadY", paras, typeptr)
       else if name.sym ∈ "fld getfld"then
            let typ=resulttype.sym  
            if iscoretype.typ then  Getfld.typ  
            else if isabstract.typ then sym 
            else
            let a=flatflds( newdict3,typ)
            assert not.isempty.a report "cannot find type getfld" +print.typ
            if length.a > 1 then 
              symbol(internalmod,"GEP", seqof.typeptr, typeint, typeptr)
            else   Getfld.first.a  
        else if name.sym ∈ "empty" then Sequence(coretype(para.module.sym, newdict3),0)
  else
        assert name.sym /in "offsets build" report "post bind error:"+print.sym
     sym
     ] 
         
         function sub5(sym2:symbol, templates:program) symdef   
                 let gx=findabstract(templates,sym2)
                   assert length.gx = 1 report"Cannot find template for X"  +
                    print.length.gx+ print.sym2  
               let newcode=   for newcode=empty:seq.symbol,sym4 = code.sd.gx_1 do  
                         assert { print.sym.sd.gx_1 /ne "set.T:+(set.T,  T)set.T"
                         /or length.print.modpara.gx_1=1 } not.isunbound.sym.sd.gx_1 report 
                        "HHH"+print.modpara.gx_1+print.sym.sd.gx_1          +print.sym4  
                      newcode+replaceTsymbol(modpara.gx_1, sym4) 
                 /for(symdef(  sym2 ,    newcode))  
              { let z=  for txt2="", sym=code.newcode do
    if print.sym /in [
      "otherseq.arcinfo.seq.word:?(arcinfo.seq.word, arcinfo.seq.word)ordering" 
     ,"otherseq.arcinfo.seq.word:binarysearch(seq.arcinfo.seq.word, int, int, arcinfo.seq.word)int "
     ,"otherseq.arcinfo.seq.word:binarysearch(seq.arcinfo.seq.word, arcinfo.seq.word)int" 
     ,"otherseq.arcinfo.seq.word:setinsert(seq.arcinfo.seq.word, arcinfo.seq.word)seq.arcinfo.seq.word " 
     ,"set.arcinfo.seq.word:asset(seq.arcinfo.seq.word)set.arcinfo.seq.word" 
     ,"svggraph.seq.word:?(seq.word, seq.word)ordering"
     ,"displaygraph.seq.word:displaygraph(characterwidths, seq.arcinfo.seq.word)seq.word"]
     then txt2+print.sym2 
   else txt2 /for(txt2)
        assert isempty.z report "LLLL"+print.sym2}
        newcode
            
 displaygraph.seq.word:displaygraph(characterwidths, seq.arcinfo.seq.word)seq.word


 function iscoretype(typ:mytype) boolean
 typ =  typeint /or typ=typereal   /or typ=typeptr /or typ=typeboolean /or isseq.typ /or isencoding.typ

  function encodenocode(typ:mytype,varno:int)seq.symbol
  let gl = symbol4(moduleref.". $global","global"_1, typ, empty:seq.mytype, seqof.typeint)
  let encodenosym = symbol(modTausupport,"encodingno", seqof.typeword, typeint)
  if typ = typeref."typename tausupport stdlib "then [  Lit.2 ]
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
            
   
   Function deepcopybody(type:mytype, typedict:typedict)seq.symbol
  if type = typeint ∨ type = typeword ∨ isencoding.type then [ Local.1]
 else if isseq.type then
 let basetype =  basetype(  type,typedict)
 if basetype = typeint ∨ basetype = typereal ∨ basetype = typeboolean then [ Local.1, blocksym.basetype]
  else
   let cat = symbol(tomodref.type,"+", [ type, parameter.type], type)
   let resulttype = basetype
   let elementtype = parameter.basetype
   let element = symbol(moduleref(". $for", elementtype),"element", empty:seq.mytype, elementtype)
   let acc = symbol(moduleref(". $for", typeptr),"acc", empty:seq.mytype, typeptr)
   [Sequence(elementtype,0)]
    + [ Local.1, acc, element, acc, element, deepcopySym( parameter.type), cat, Littrue, acc, symbol(builtinmod( typeint),"forexp", [ resulttype, resulttype, resulttype, elementtype, typeptr, typeboolean, resulttype], resulttype)
    ]
    + blocksym.basetype
 else
  let subflds =  flatflds(typedict,type)
  if length.subflds = 1 then
    { only one element in record so type is not represent by actual record }[ Local.1]
    + deepcopySym(first.subflds)
   else 
    for     fldno=1, fldkinds=empty:seq.mytype, result= empty:seq.symbol,fldtype=subflds do
  let kind = basetype(  fldtype,typedict)
   next(fldno+1,fldkinds + kind, result + [ Local.1,Lit(fldno - 1), Getfld.kind,   deepcopySym( fldtype)])
/for(result + [ Record.fldkinds])
      
 Function blocksym(basetype:mytype)symbol
let p = parameter.basetype
let p2 = seqof.if p = typebyte ∨ p = typebit ∨ p = typeboolean then typeint else p
 symbol(modTausupport,"blockIt", p2, p2)

 
use set.passsymbols

use seq.modref

use set.modref

          
   
       type debug is data:seq.word,k:int
    
 function    hash (d:debug) int hash.data.d
 
 function   assignencoding(l:seq.encodingpair.debug,debug) int length.l
 
 use seq.encodingpair.debug 
 
 
 
 use encoding.debug
 
 function =(a:debug,b:debug) boolean data.a=data.b
        
