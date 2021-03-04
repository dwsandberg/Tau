#!/usr/local/bin/tau  ; use bug9; xxx33

module mergeblocks

use standard 

use graph.bbnode

use seq.arc.bbnode

use symbol

use seq.symbol

use seq.bbnode

 use stack.seq.arc.bbnode
 
 use otherseq.seq.arc.bbnode
 
 use otherseq.int      
     

use set.arc.bbnode

  use otherseq.bbnode
  
  use set.bbnode

type   bbnode  is nodeno:int,code:seq.symbol,kind:word,brt:int,brf:int

function  nodebr(idx:int, code:seq.symbol,t:int,f:int ) bbnode
  let exp=last.code
  if  exp=NotOp then
   nodebr(idx,code >> 1 ,f,t)
else if exp=Littrue then 
   bbnode(idx,code >> 1 ,"br"_1,t,t)
else if exp=Litfalse then 
    bbnode(idx,code >> 1 ,"br"_1,f,f)
else   bbnode(idx,code,"br"_1,t,f)
 
function arc(b:bbnode) seq.arc.bbnode  [arc(b,b)]


function print(a:set.bbnode) seq.word for acc="",t =toseq.a do acc+print.nodeno.t end(acc) 
 
Function =(a:bbnode,b:bbnode) boolean nodeno.b = nodeno.a

Function ?(a:bbnode,b:bbnode) ordering nodeno.b ? nodeno.a


Function mergeblocks(code:seq.symbol)  graph.bbnode
  for   start=1,idx=1
     ,stk=empty:stack.seq.arc.bbnode
     ,lastsymbol=Lit.0
     ,bbcode=empty:seq.symbol
     , sym=code do 
        if isblock.sym then
         \\ do not include block symbol in basic block \\
          next( idx+1,idx+1,stk ,sym, empty:seq.symbol )
        else 
        \\ handle block followed by exit or Br differently than block not followed by Exit or Br \\
          let merge=  isblock.lastsymbol &and (sym=Exit &or isbrz.sym )
             &and  kind.head.first.first.top(stk, nopara.lastsymbol) &ne "loop"_1
        \\  deal with last symbol being block if we are not merging it. \\
          let stk1 = if merge then stk
                      else if isblock.lastsymbol   then 
                        pop(stk,nopara.lastsymbol)
                     else stk
            let  bbcode1=if merge then empty:seq.symbol 
               else if isblock.lastsymbol   then 
               bbcode+flattennodes(toseq.nodes.makegraph.toarcs(lastsymbol,top(stk, nopara.lastsymbol)),resulttype.lastsymbol)  
               else bbcode
          \\ now deal with sym and merge \\
          let stk2= if isbrz.sym then 
           let a=bbnode(idx,empty:seq.symbol,"brz"_1,toint.(fsig.sym)_2 ,toint.(fsig.sym)_3 )
                  let noblks=nopara.lastsymbol
                push(pop(stk,noblks ),toarcs(lastsymbol,top(stk, noblks))+arc.a)
          else if sym=Br then
              push(stk1, arc.nodebr(idx, bbcode1+subseq(code,start,idx-3),value.code_(idx-2),value.code_(idx-1))   )
           else if  isloopblock.sym then
             push(stk1, arc.bbnode(idx,  bbcode1+subseq(code,start,idx ),"loop"_1,0,0 ))
           else if  iscontinue.sym then
             push(stk1, arc.bbnode(idx,  bbcode1+subseq(code,start,idx ),"continue"_1,0,0 ))
           else if sym=Exit then
             if  merge then 
               let noblks=nopara.lastsymbol
               push(pop(stk,noblks ),toarcs(lastsymbol,top(stk, noblks)))
             else 
               push(stk1, arc.bbnode(idx,  bbcode1+subseq(code,start,idx ),"exit"_1,0,0 ))
           else stk1 
          let start2= if length.toseq.stk1=length.toseq.stk2 then start else idx+1
          let bbcode2= if length.toseq.stk1=length.toseq.stk2 &or merge then 
            bbcode1 else 
           empty:seq.symbol 
         next( start2,idx+1,stk2,sym, bbcode2)
    end (  
    if isblock.lastsymbol then makegraph.toarcs(lastsymbol,top(stk, nopara.lastsymbol)  )
      else 
      let t= (arc.bbnode(idx,  bbcode+subseq(code,start,idx )+Exit,"exit"_1,0,0 )) _1
       deletearc(newgraph.[t] ,t))
           

function   print(a:seq.seq.arc.bbnode) seq.word 
   for acc="",t = a do  acc+"{"+print.t+"}" end(acc)
 
   
 
function print(a:seq.arc.bbnode ) seq.word
     for acc="",t =  a do
  acc+"("+print.nodeno.tail.t+print.nodeno.head.t+")"
   end(acc)
   
function  toarcs   (sym:symbol,nodes:seq.seq.arc.bbnode) seq.arc.bbnode
    for  acc=empty:seq.arc.bbnode,blkno=nopara.sym,nodelist=empty:seq.bbnode , nl=reverse.nodes do 
         let n=tail.nl_1
         if  length.nl=1 &and head.nl_1=n then
         let kind= kind.n
          if kind="br"_1 then 
                let brancht=  nodelist_(brt.n - blkno)
                let branchf=  nodelist_(brf.n - blkno)
                let new=  bbnode( nodeno.n,code.n,kind.n,nodeno.brancht,nodeno.branchf)
              next(  acc+[arc(new,brancht),arc(new,branchf)],blkno-1,[new]+nodelist)
           else if kind="loop"_1 then
              next( acc+arc(n,first.nodelist),blkno-1, [n]+nodelist)
            else \\ exit continue\\
             next(acc,blkno-1, [n]+nodelist) 
        else 
          let toadd= if kind.head.last.nl &ne "brz"_1 then nl else 
            let bb=head.last.nl
          let brancht=   nodelist_(brt.bb - blkno)
          let branchf=   nodelist_(brf.bb - blkno) 
           for acc2=empty:seq.arc.bbnode, arc = nl >> 1 do
               if kind.head.arc="exit"_1 then 
                  if code.head.arc >> 1 =[Littrue] then
                   acc2+arc(tail.arc,branchf)
                  else if code.head.arc >> 1 =[Litfalse] then
                   acc2+arc(tail.arc,brancht)
                  else 
                 let new=nodebr(nodeno.head.arc,code.head.arc >> 1,nodeno.brancht,
                 nodeno.branchf)
                   acc2+  arc(tail.arc,new)+arc(new,brancht)+arc(new,branchf)    
               else acc2+arc
            end(  acc2)
           next(acc+toadd,blkno-1,[n]+nodelist)
        end  (acc)
        
Export kind(bbnode) word

Export code(bbnode) seq.symbol 

Export type:bbnode     

Export brt(bbnode) int

 Export brf(bbnode) int
 
 Export bbnode(int, seq.symbol, word, int, int) bbnode
 
 Export nodeno(bbnode) int
 
   
function  makegraph(a:seq.arc.bbnode) graph.bbnode
  let g0=newgraph.a
    \\ remove unreachable nodes \\
  let b=      for g=g0,n=toseq(nodes.g0-reachable(g0, [last.toseq.nodes.g0] ) ) do deletenode(g,n) end (g)
  \\ remove chains \\
   for  g=b, n = toseq.nodes.b   do 
         if kind.n="loop"_1 then g else 
        let s=successors(g,n)
       if cardinality.s &ne 1 then g
       else 
         \\ n may not be the same as predcessors(g,s_1)_1 as the nodes of b might not have 
         identicial information to the nodes in g \\
             removechain(g,predecessors(g,s_1)_1,empty:seq.symbol,predecessors(g,n),nodeno.n) 
    end(g)

use otherseq.seq.int
   
     
Function flattennodes( nodes:seq.bbnode,type:mytype) seq.symbol
 \\ nodes are numbered in order they appear in orignal code.  This many be different from the order they appear in the funcion parameter
 which is the reverse order they will appear in the output \\
 if length.nodes=1 then   
         code.(nodes)_1  >> 1 
else  let blocksize=length.nodes
    let nodenumbers=for  acc=empty:seq.int, n = nodes do  [nodeno.n]+acc end(acc)
    for acc=empty:seq.symbol,n =nodes do
           if kind.n="br"_1 then  code.n +Lit.findindex(brt.n,nodenumbers )+Lit.findindex(brf.n,nodenumbers )+Br  else  
          code.n fi+acc
       end (acc+Block(type,length.nodenumbers) )

function removechain(     g:graph.bbnode,n:bbnode,code:seq.symbol,pred:set.bbnode,
 org:int) graph.bbnode
      let newcode=code+code.n
     let s=successors(g,n)
     if cardinality.s = 1  &and cardinality.predecessors(g,s_1)=1 then  
        removechain( deletenode(g,n),s_1,newcode,pred,org)
     else 
       let newnode= \\if isempty.code then n else \\bbnode( org,newcode,kind.n,brt.n,brf.n)
        deletenode(g,n)+newnode+toarcs(toseq.pred,newnode)+toarcs(newnode,toseq.s)
           
Function Brz(t:int,f:int) symbol   symbol( "brz"+toword.t+toword.f+"(boolean)" ,"$brz","none")
       
function isbrz(s:symbol) boolean module.s="$brz"



