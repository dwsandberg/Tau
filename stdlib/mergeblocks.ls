module mergeblocks2

use standard

use symbol

use seq.symbol
             
use stack.int

use otherseq.symbol

use seq.int

type ggg is code:seq.symbol,stk:stack.int

    function countnodes2(s:stack.int) int
    if top.s =2 then 1 else 1+countnodes2(pop.s)

    
Function valid(s:seq.symbol) boolean
 for  valid=true,  stk=empty:stack.int,sym=s while valid do
   if isblock.sym then
       let noblocks=countnodes2(stk)
      next(top.stk &le noblocks,pop(stk,noblocks) )
   else if isbr.sym then
      let blkno=countnodes2(stk)+1 
       next(  brt.sym > 0 &and brf.sym > 0, push(stk,max(blkno+max(brt.sym,brf.sym),top.stk)) )
   else  if first.module.sym &in "  $exitblock $continue " then  
          next(valid,push(stk,top.stk) )
        else if isstartorloop.sym  then  next(valid,push(stk,2) )
       else  next(valid,stk)
 end (valid)

function   ghj(code:seq.symbol,stk:stack.int,label:int,replace:int) seq.symbol
   if top.stk < 0 then code
   else 
    let sym= code_top.stk
     \\  assert not.isbr.sym report "TFL"+print.brt.sym+print.brf.sym+print.label +print.replace \\
 let newcode=    if isbr.sym &and (label=brt.sym &or label=brf.sym) then
       replace(code,top.stk,Br2(if label=brt.sym then replace else brt.sym,
        if label=brf.sym then replace else brf.sym))
    else code
  ghj(newcode,pop.stk,label+1,replace+1)

  use set.int
  

  
  function unreached(code:seq.symbol,nodes:seq.int) seq.symbol 
  let unreached=  for unreached=empty:seq.int, targets=asset.[2],count=2, n=nodes << 1 do
       let sym=code_n
       if  count &nin targets then
         next( [count]+unreached,targets,count+1)
       else if isbr.sym then
         next(unreached,targets+(count+brf.sym)+(count+brt.sym),count+1)
       else next(unreached,targets,count+1)
    end(unreached)
 if length.nodes-3=length.unreached 
   &and isstart.code_-first.nodes then
     \\ just two active nodes which must be a branch follow by an exit.
       so remove block \\ 
     let blkstart=-first.nodes 
     let secondnode=code_(nodes_2)
    subseq(code,1,blkstart-1)+
            subseq(code,blkstart+1,(nodes_2)-2)
            + subseq(code, nodes_(1+brt.secondnode)+1,nodes_(2+brt.secondnode)-1)
  else  for   newcode=code,   n = unreached  do
            adjustbr(subseq( newcode,1, nodes_(n-1)),subseq(nodes,2,n-1)  ,-1)
                  +subseq(newcode,nodes_n+1,length.code) 
        end(newcode+EndBlock)                                 
    

Function optB(s:seq.symbol,self:symbol) seq.symbol
   for acc=empty:seq.symbol,stk= empty:stack.int ,lastsymbol=Lit.0 ,sym =s do
   if (lastsymbol =Littrue &or lastsymbol=Litfalse) &and isbr.sym &and top.stk=length.acc-1 then 
   \\ patch previous br's so they skip over this block \\
      next(ghj(acc , stk,1,1+if lastsymbol=Littrue then brt.sym else brf.sym   )+sym, push(stk,length.acc+1),sym)
  else  if isblock.sym then
    next(acc,stk,sym)
  else if not.isblock.lastsymbol then
       next(acc+sym,newstk(sym,stk,acc),sym)
    else \\ lastsymbol isblock \\
        let noblocks=countnodes(stk)
        let nodes=top(stk,noblocks)
        let stk1=pop(stk,noblocks)
        let blkstart=-first.nodes
        if isloopblock.acc_blkstart  &or  ( sym &ne Exit &and not.isbr.sym) then 
           let code0=unreached(acc,nodes) 
         next(code0+sym,newstk(sym,stk1,code0),sym)
     else   if   isbr.sym  then    
      \\  assert  noblocks &ne 4 report "X"+print.noblocks +print.length.s  \\
           \\ adjust br in enclosing block  \\
           let code0=adjustbr(acc  ,top( stk1,countnodes.stk1 -1),noblocks-2)
         \\ remove start of block   \\
           let code1=subseq(code0,1,-first.nodes-1)
           + subseq(code0,-first.nodes+1,length.code0)
               \\  replace exit by br sym \\
        let t=for   code2=code1,stk2=stk1 ,adjust=noblocks-2 , n1 = nodes << 1
        do 
          let n=n1-1
            next(  if code2_n=Exit then 
             if  top.stk2=n-2 &and code2_(n-1)=Littrue then 
                 let  code3=ghj(code2 , stk2,1,brt.sym+adjust+1  )
              replace(code3,n,  Br2(brt.sym+adjust,brt.sym+adjust)  ) 
             else if  top.stk2=n-2 &and code2_(n-1)=Litfalse then 
                 let  code3=ghj(code2 , stk2,1,brf.sym+adjust+1  )
              replace(code3,n,  Br2(brf.sym+adjust,brf.sym+adjust)  ) 
             else 
             replace(code2,n,  Br2(brt.sym+adjust,brf.sym+adjust)  ) 
            else code2,push(stk2,n)
            ,adjust-1)
         end( ggg(code2, stk2 )  )
         next(code.t,stk.t,sym)
     else   
       assert  sym=Exit report "Expected Exit" 
         \\  adjust br in enclosing block  \\
          let code0=adjustbr(acc  ,top( stk1,countnodes.stk1 -1),noblocks-2)
        \\ remove start of block   \\
           let code1=subseq(code0,1,-first.nodes-1)
           + subseq(code0,-first.nodes+1,length.code0)
         \\   build new stk  \\
       let stk2=  for stk2=stk1 ,  n = nodes << 1 do           push(stk2,n-1) 
         end( stk2)
         next(code1,stk2,sym)
       end( if isblock.lastsymbol then
           if  not.isconst.self &and first.toseq.stk=-1 then tailR(acc+lastsymbol,self,stk)
           else unreached(acc,toseq.stk)
          else 
           acc
        )
         
function    newstk(sym:symbol,stk:stack.int,acc:seq.symbol) stack.int    
   if isstartorloop.sym then push(stk,-length.acc-1)
   else  if first.module.sym &in " $br  $exitblock $continue" then
      push(stk,length.acc+1)
   else stk
    
         
    function tailR(code:seq.symbol,self:symbol,stk:stack.int) seq.symbol
      let l= for l=empty:seq.int,ss=toseq.stk do  
           if ss > 0 &and code_ss = Exit &and code_(ss-1)=self then  [ss]+l  else l 
        end(l)
        if isempty.l then code else
        let nopara=nopara.self
        let plist = for acc = empty:seq.symbol, e2 = arithseq(nopara, 1, 1)do   acc + Local.e2 end(acc)
        let code2=  for code2=code, i = l do
             subseq(code2,1,i-2)+continue.nopara+subseq(code2,i+1,length.code2)
           end(code2)
         plist 
 +Loopblock(paratypes.self,nopara+1 ,resulttype.self) + adjustvar(code2 << 1,nopara)
       
function adjustvar(s:seq.symbol, delta:int)seq.symbol
 for  acc=empty:seq.symbol, a =s do
    if islocal.a then
      acc+Local(toint.(fsig.a)_1 + delta) 
   else if isdefine.a then
      acc+Define.toword(toint.(fsig.a)_2 + delta) 
   else if isloopblock.a then
      acc+Loopblock(paratypes.a,firstvar.a + delta,resulttype.a)
     else acc+a
    end  (acc)
    
 
 function adjustbr(code:seq.symbol,nodestoadjust:seq.int,adjust:int) seq.symbol
  \\ if branch target is not in nodestoadjust then it is adjusted \\
  \\ nodes to adjust does not include block start node \\
     for acc=code,     blockcount=length.nodestoadjust   , i=nodestoadjust do
       let sym=acc_i 
      if  isbr.sym &and (brt.sym > blockcount &or brf.sym > blockcount) then
        let newt=if brt.sym > blockcount  then brt.sym+adjust else brt.sym
        let newf=if brf.sym > blockcount  then brf.sym+adjust else brf.sym
           next( replace(acc,i,Br2(newt,newf)),blockcount-1)
      else 
         next( acc,blockcount-1)
    end(acc)         



function countnodes(s:stack.int) int
    if top.s < 0 then 1 else 1+countnodes(pop.s)
    
Function removeismember(c:symbol,var:symbol) seq.symbol
 if module.c="$words" then 
    let words= fsig.c
    if isempty.words then [Litfalse] else 
    let t=length.words+2
    if length.words=1 then [var,Word.words_1,EqOp] 
    else
      for acc=[start(mytype."boolean")],idx=2,w = words >> 1   do 
         next(acc+[var,Word.w,EqOp]+Br2(t-idx,1) ,idx+1)
     end(acc+[var,Word.last.words,EqOp,Exit,Littrue,Exit,EndBlock ])  
  else
     let z=constantcode.c << 2
     if isempty.z then [Litfalse] else
     let t=length.z +2
     for acc=[start(mytype."boolean")],idx=2,w = z >> 1   do 
       next(acc+[var,w,EqOp]+  Br2( t-idx, 1  ) ,idx+1)
      end(acc+[var, last.z,EqOp,   Exit,Littrue,Exit
              ,EndBlock])

