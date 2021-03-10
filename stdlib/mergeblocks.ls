module mergeblocks2

use standard

use symbol

use seq.symbol
             
use stack.int

use otherseq.symbol

Function cvtR(s:seq.symbol) seq.symbol
   for acc=empty:seq.symbol,stk=push(empty:stack.int,0) ,sym =s do
    if isstartorloop.sym &or sym=Exit &or isbr.sym &or iscontinue.sym then 
      next(acc+sym,push(stk,length.acc+1) )
    else if not.isblock.sym then 
      next(acc+sym,stk )
    else 
     let k=top(stk,nopara.sym)
     let modbr=for  acc2=acc,   idx=1,   n=k do
        let new= if isbr.acc2_n then  
           replace(acc2, n,Rbr(brt.acc2_n-idx,brf.acc2_n-idx))
         else  acc2
          next(new,idx+1)
        end (acc2)
         let j=undertop(stk,nopara.sym)
         if   isstartorloop.modbr_first.k then
            next(modbr+sym,pop(stk,nopara.sym))
          else 
           assert isbr.modbr_first.k report "cvtR"
            let j2= backparse(modbr,first.k,1,empty:seq.int)_1  -1
            let g= subseq(modbr,1,j2)+start(resulttype.sym)+subseq(modbr,j2+1,length.modbr)+Block(resulttype.sym,nopara.sym+1)
      next(g ,pop(stk,nopara.sym))
    end(acc)

function backparse(s:seq.symbol, i:int, no:int, result:seq.int)seq.int
 if i > 0 &and isdefine.s_i then
   let args = backparse(s, i - 1, 1, empty:seq.int)
    backparse(s, args_1, no, result)
   else
   if no = 0 then result
 else
  assert i > 0 report"back parse 1:" + toword.no + print.s + stacktrace
    let nopara = nopara.s_i
    let first = if nopara = 0 then 
    i
    else
     let args = backparse(s, i - 1, nopara, empty:seq.int)
      assert length.args = nopara report"back parse 3" + print.[ s_i] + toword.nopara + "//"
      + for acc ="", @e = args do acc + toword.@e end(acc)
       args_1
    let b = if first > 1 ∧ isdefine.s_(first - 1)then
    let c = backparse(s, first - 2, 1, empty:seq.int)
     c_1
    else first
     backparse(s, b - 1, no - 1, [ b] + result)
 

type  p56 is  count:int,type:mytype

use stack.p56



Function  undoR(s:seq.symbol,fixblockcount:boolean) seq.symbol
 for acc=empty:seq.symbol,stk=empty:stack.p56,count=1,sym =s do 
     if  isstart.sym  then
         if fixblockcount then
          next(acc+sym,push( stk,p56( count,resulttype.sym)),2) 
         else 
          next(acc,push( stk,p56( count,resulttype.sym)),1) 
     else     if  isloopblock.sym then
          next(acc+sym,push( stk,p56( count,resulttype.sym)),2) 
     else if isbr.sym then
        \\  if fixblockcount then
                next(acc+Br2(brt.sym ,brf.sym ),stk,count+1)
          else \\
        next(acc+Br2(brt.sym+count,brf.sym+count),stk,count+1)
     else if  last.module.sym &in "$exitblock $continue" then
         next(acc+sym,stk,count+1)
     else if isblock.sym then 
        next(acc+Block( type.top.stk ,count-1),pop(stk ),count.top.stk)
     else next(acc+sym,stk,count)
end( acc)

use seq.int

type ggg is code:seq.symbol,stk:stack.int

Function optB(s:seq.symbol,self:symbol) seq.symbol
   for acc=empty:seq.symbol,stk= empty:stack.int ,lastsymbol=Lit.0 ,sym =s do
  if isblock.lastsymbol then
        let noblocks=countnodes(stk)
        let nodes=top(stk,noblocks)
        let stk1=pop(stk,noblocks)
        let blkstart=-first.nodes
      if isloopblock.acc_blkstart then
          next(acc+sym,stk1,sym)
     else  
       let secondnode=acc_(nodes_2) 
       if isbr.secondnode &and brt.secondnode =brf.secondnode 
         &and Exit=acc_(nodes_(2+brt.secondnode)) then
              let newacc= 
            subseq(acc,1,blkstart-1)+
            subseq(acc,blkstart+1,(nodes_2)-2)+ subseq(acc, nodes_(1+brt.secondnode)+1,nodes_(2+brt.secondnode)-1)
           \\     assert false report 
            "NLES"+print.newacc +EOL+EOL+EOL+print.acc  \\
        if first.module.sym &in "  $br  $exitblock $continue " then
          next(newacc+sym,push(stk1,length.newacc+1),sym)
        else if isstartorloop.sym  then
          next(newacc+sym,push(stk1,-length.newacc-1),sym)
        else next(newacc+sym,stk1,sym)
     else    if false &and isbr.sym then
           \\ adjust br in enclosing block  \\
          let code0=adjust(acc >> 1,stk1,  noblocks-2)
         \\ remove start of block   \\
           let code1=subseq(code0,1,-first.nodes-1)
           + subseq(code0,-first.nodes+1,length.code0)
               \\  replace exit by br sym \\
        let t=for   code2=code1,stk2=stk1 ,adjust=noblocks-2 , n1 = nodes << 1
        do 
          let n=n1-1
            next(  if code2_n=Exit then replace(code2,n,  Rbr(brt.sym+adjust,brf.sym+adjust)  ) else code2,push(stk2,n)
            ,adjust-1)
         end( ggg(code2, stk2 )  )
         next(code.t,stk.t,sym)
     else   if sym=Exit then 
         \\  adjust br in enclosing block  \\
          let code0=adjust(acc >> 1,stk1, noblocks-2)
        \\ remove start of block   \\
           let code1=subseq(code0,1,-first.nodes-1)
           + subseq(code0,-first.nodes+1,length.code0)
         \\   build new stk  \\
       let stk2=  for stk2=stk1 ,  n = nodes << 1 do           push(stk2,n-1) 
         end( stk2)
         next(code1,stk2,sym)
     else   if first.module.sym &in "  $br  $exitblock $continue " then
          next(acc+sym,push(stk1,length.acc+1),sym)
     else if isstartorloop.sym  then
          next(acc+sym,push(stk1,-length.acc-1),sym)
     else next(acc+sym,stk1,sym)
 else   
    if isstartorloop.sym then
     next(acc+sym,push(stk,-length.acc-1),sym)
    else if first.module.sym &in " $br  $exitblock $continue" then
        next(acc+sym,push(stk,length.acc+1),sym)
    else next(acc+sym,stk,sym)
       end( if isblock.lastsymbol &and not.isconst.self
          &and first.toseq.stk=-1 then tailR(acc,self,stk)
          else 
           acc
        )
         
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
    
function adjust(code:seq.symbol,stk:stack.int, adjust:int) seq.symbol
     let c=countnodes.stk -1
     for acc=code,     blockcount=c   , i=top( stk,c) do
      let sym=code_i
      if  isbr.sym &and (brt.sym > blockcount &or brf.sym > blockcount) then
        let newt=if brt.sym > blockcount  then brt.sym+adjust else brt.sym
        let newf=if brf.sym > blockcount  then brf.sym+adjust else brf.sym
        assert true report "here"+ print.newf+print.brf.sym+print.adjust+print.blockcount
         +for l="stk",e= toseq.stk do l+print.e end(l)
         next( replace(code,top.stk,Rbr(newt,newf)),blockcount-1)
      else 
         next( code,blockcount-1)
    end(acc)         

function countnodes(s:stack.int) int
    if top.s < 0 then 1 else 1+countnodes(pop.s)

  