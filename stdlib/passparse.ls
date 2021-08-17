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
            /or  name.module.codesym /in "builtin" then arcs
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
        
                 for acc=empty:seq.arc.symbol,  a=toseq.arcs.transitiveClosure.g do
     if head.a /in  toprocess then acc+a else acc /for( acc)

       

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
            symbol(moduleref("builtin", typeT), [ wordname.sym], paratypes.sym, resulttype.sym)
      else symbol4(moduleref("builtin", typeT), wordname.sym,(nametype.sym)_1, paratypes.sym, resulttype.sym)]
       )
           else 
               assert first.text.p /in "Function function" report text.p
      let b=  parse( src_paragraphno.p,partdict,z)
         symdef(sym.p, parsedcode.b,paragraphno.p ) 
       /for( prg+acc )
      /for(  prg   )
      
       
  use symboldict     
    
Function  passparse(   abstractmods :set.passsymbols,simplemods:set.passsymbols
,lib:word, prg1:seq.symdef
,src:seq.seq.word,mode:word) 
set.symdef
 let allmods=abstractmods /cup simplemods
 let prga=compile(allmods, abstractmods ,lib  ,src ,mode,empty:set.symdef) 
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
let g5=for  acc=g4,  n=toseq(sinks /cap nodes.g4)   do 
let newgraph=if isunbound.n then acc else  deletenode(acc,n)
  let f=findabstract(templates,n)
  {assert not.isempty.f report "analzye templates error"+print.n}
  if isempty.f then newgraph
   else
    { look in g4 to find what unbound symbols are used }
  for acc2=empty:seq.arc.symbol,sym=toseq.successors(g4,sym.f_1) do 
     let x=replaceTsymbol(modpara.f_1,sym)
      acc2+ toarcs( toseq.predecessors(g4,sym.f_1)  ,x ) /for(newgraph+acc2) 
/for(acc)
 let check=  for txt="",  n=toseq(sinks /cap nodes.g5) do
     if isunbound.n /or para.module.n=typeT then txt 
      else txt+print.n /for(txt)
assert isempty.check report "CHECK"+check
 { change many-to-one relation defined by arcs in g5 into format of set.symdef }
  let requireUnbound=if isempty.arcs.g5 then empty:set.symdef else 
  for acc=empty:set.symdef
     , last=Lit.0
     ,list=empty:seq.symbol,a=toseq.arcs.g5 do
   if last /ne tail.a then
          next(if isempty.list then acc else   acc+symdef(last,list)
          , tail.a,if isunbound.head.a then [head.a] else empty:seq.symbol)
     else next(acc, tail.a,if isunbound.head.a then list+head.a else list)
  /for(if isempty.list then acc else   acc+symdef(last,list))
  { assert isempty.requireUnbound  report "req"+for acc="",x=toseq.requireUnbound do acc+print.sym.x +print.code.x+EOL
  /for(acc)  }
  let discard10= requirematch
  let prg=compile(allmods, simplemods ,lib  ,src ,mode,requireUnbound)
 asset(  prga+prg1+  prg +requirematch)
 
     
 
 use seq.seq.mytype
 
               use set.word
               
  
   
  use typedict
       
  function  abstractSymbolUses(z:seq.symbol) set.symbol  
       for acc =empty:set.symbol,sym=z do
         if issimple.module.sym then 
           if not.isconst.sym /and istype.sym then 
              acc+sym
           else acc 
         else if name.module.sym  /in "$for" then
              if name.sym /in "next for" then acc
              else 
                let  idxsym=symbol(moduleref("stdlib seq",resulttype.sym),"_",seqof.resulttype.sym,typeint,resulttype.sym)
                acc+idxsym
        else if  name.module.sym  /in "builtin $local  $word $words $int $boolean   $br2   $define internal
  $sequence  $typefld $loopblock"    
  then acc 
  else  acc+sym 
/for(acc)

  
 /  use displaytextgraph

 / use svggraph.seq.word

/ use seq.arcinfo.seq.word

/ function arcinfo(l:seq.arc.symbol) seq.arcinfo.seq.word
     for acc=empty:seq.arcinfo.seq.word,a=l do 
    acc+arcinfo(print.tail.a ,print.head.a,"")
    /for(acc)
   

 
 use words

use otherseq.mytype




               
          
            