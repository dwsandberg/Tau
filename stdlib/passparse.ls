 module passparse 
 
 use passsymbol

 use symbol
  
 use mytype
 
 use standard
 
 use seq.symtextpair

 use set.passsymbols
 
 use set.passtypes
 
 use seq.symdef
 
 use set.modref
 
 use set.mytype
 
 use set.symdef
 
 use set.symbol
 
 use seq.symbol
 
 use graph.symbol
 
 use seq.arc.symbol
 
 use graph.seq.word
 
 use seq.findabstractresult

use parse

use set.arc.symbol

use encoding.symbol


 function abstractarcs(s: seq.symdef ) seq.arc.symbol
   for outer=empty:seq.arc.symbol,p=s do 
        let sym=sym.p
         for arcs=outer,codesym =  code.p    do 
           if isspecial.codesym /or not.isabstract.module.codesym /or sym  = codesym 
            /or   isBuiltin.codesym  then arcs
             else  if name.module.codesym /in "$for" then 
            if name.codesym /in "name for" then arcs
            else
                arcs+arc(sym,symbol(moduleref("stdlib seq",resulttype.codesym),"_",seqof.resulttype.codesym
             ,typeint,resulttype.codesym))
          else 
           arcs+arc(sym ,codesym) 
        /for (arcs)
    /for(outer)
        
        function print(a:arc.symbol)  seq.word  print.tail.a+print.head.a  
        
          
        use program
        
 
       

function removesinks(      sinkstokeep:set.symbol,g:graph.symbol,toprocess:seq.symbol)
     seq.arc.symbol
    { removes sinks that are not unbound and parameter of module is typeT}
    { do a transitiveClosure and only keep arcs whose head is a sink }
    { looking for relation of function to the unbound functions it can call.
     This are not quite yet that relation. } 
      for keep=sinkstokeep,  pred=empty:set.symbol,g2=g,  n=toprocess do 
        if isunbound.n /or para.module.n /ne typeT  then next(keep+n, pred,g2)
        else  next(keep,pred /cup predecessors(g2,n),deletenode(g2,n))
       /for(  
          let newsinks=for  acc=empty:seq.symbol,   p=toseq.pred do
            if  outdegree(g,p)=0 then acc+p else acc 
         /for(acc)
           if isempty.newsinks  then
              for acc=empty:seq.arc.symbol,  a=toseq.arcs.transitiveClosure.g2 do
     if head.a /in  keep then acc+a else acc /for( acc)
          else removesinks(keep,g2,newsinks)
       ) 
       
Function  compile( allmods:set.passsymbols,  modlist :set.passsymbols,lib:word
,src:seq.seq.word,mode:word,requireUnbound:set.symdef ) 
seq.symdef       
   for  prg=empty:seq.symdef,  m=toseq.modlist do 
     let z= commoninfo("", modname.m, lib , typedict.m, mode)
          let partdict=formsymboldict(allmods,m,requireUnbound,mode)   
       for  acc=empty:seq.symdef ,      p=text.m do
         acc+if first.text.p /in "Builtin builtin"  then  
               let sym=sym.p
                symdef(sym.p
                 ,for code = empty:seq.symbol, @e = arithseq(nopara.sym.p, 1, 1)do 
                    code + Local.@e 
                 /for( code)
                   + if issimple.module.sym.p then [ sym.p, Words."BUILTIN", Optionsym]
                    else
      [ if issimplename.sym then 
          assert isabstract.module.sym /or  name.sym /in " loadlib  
addresstosymbol2 callstack randomint currenttime
getmachineinfo createlib2 getfile getbytefile getbitfile
addencoding getinstance allocatespace dlsymbol loadedlibs  unloadlib
tan cos sin sqrt arcsin arccos
 unloadlib   createfile 
"   report "xxx"+print.sym
            symbol(builtinmod( typeT), [ wordname.sym], paratypes.sym, resulttype.sym)
      else symbol4(builtinmod( typeT), wordname.sym,(nametype.sym)_1, paratypes.sym, resulttype.sym)]
       )
           else 
               assert first.text.p /in "Function function" report text.p
      let b=  parse( src_paragraphno.p,partdict,z)
         symdef(sym.p, code.b,paragraphno.p ) 
       /for( prg+acc )
      /for(  prg   )
      
       
  use symboldict     
    
Function  passparse(   abstractmods :set.passsymbols,simplemods:set.passsymbols
,lib:word, prg1:seq.symdef
,src:seq.seq.word,mode:word) 
set.symdef
 let allmods=abstractmods /cup simplemods
 let prga=prescan2.compile(allmods, abstractmods ,lib  ,src ,mode,empty:set.symdef) 
  let g3=  newgraph.abstractarcs( prga+prg1 ) 
{ graph g3 has three kinds of sinks.
     1:is unbound and module parameter is T
     2: is not unbound and module parameter is T
     3:   module parameter is not T
    examples: otherseq.T:=(T, T) boolean ; otherseq.T:step(arithmeticseq.T)T ;
      otherseq.sparseele.T:binarysearch(seq.sparseele.T) }
  let sinks =asset.sinks.g3
 let g4=     newgraph.removesinks(empty:set.symbol,g3,toseq.sinks)
  let templates=for acc=empty:set.symdef, sd=prga do
       if isabstract.module.sym.sd then acc+sd else acc 
   /for(program(asset.prg1 /cup acc))
 { change many-to-one relation defined by arcs in g5 into format of set.symdef }
  let requireUnbound=if isempty.arcs.g4 then empty:set.symdef else 
  for acc=empty:set.symdef
     , last=Lit.0
     ,list=empty:seq.symbol,a=toseq.arcs.g4 do 
     let list0=if last /ne tail.a then empty:seq.symbol else list
       let newlist=if isunbound.head.a then list0+head.a else  list0
      let newacc=if last /ne tail.a then
      if isempty.list then acc else  
            acc+symdef(last,list) else acc
          next(newacc , tail.a,   newlist)
  /for(if isempty.list then acc else   acc+symdef(last,list))
   let prg=compile(allmods, simplemods ,lib  ,src ,mode,requireUnbound)
 asset(  prga+prg1+  prg )
 
     function  prescan2(  s: seq.symdef) seq.symdef
      for  acc=empty:seq.symdef ,  p=s  do
         for  result = empty:seq.symbol, sym = code.p do
           if  islocal.sym then
                 result +  Local.value.sym
           else if isdefine.sym then  result+Define.value.sym
           else {if isconst.sym /or isspecial.sym then result+sym
           else
              assert subseq(print.sym.p,1,5) /ne  "tree.T:="  /or module.sym.p=module.sym report 
          "KL"+print.sym.p+ print.sym}
           result + sym
      /for(acc+symdef( sym.p,result))
      /for( acc)  
   
 
 use seq.seq.mytype
 
use set.word

 use words

use otherseq.mytype
            
  use typedict
  
  
 /  use displaytextgraph

 / use svggraph.seq.word

/ use seq.arcinfo.seq.word

/ function arcinfo(l:seq.arc.symbol) seq.arcinfo.seq.word
     for acc=empty:seq.arcinfo.seq.word,a=l do 
    acc+arcinfo(print.tail.a ,print.head.a,"")
    /for(acc)
   

  

               
          
            