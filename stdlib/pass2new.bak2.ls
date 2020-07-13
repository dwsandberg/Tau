#!/usr/local/bin/tau


Module pass2new

run mylib testnew 

run mylib test


type block is record kind:word,blkno:int,label1:int,label2:int,code:seq.symbol,subblks:seq.block


function block(kind:word,blkno:int,label1:int,label2:int,code:seq.symbol) block
  block(kind,blkno,label1,label2,code,empty:seq.block)

use seq.block

use stack.block


function breakblocks(p:program,code:seq.symbol,self:symbol) seq.symbol  
  let a=breakblocks(p,code,1,1,empty:seq.symbol,empty:stack.block)
  if length.a=1 then code.a_1 else 
   if not(kind.a_1="LOOPBLOCK"_1) &and @(&or,tailrecursion.self,false,a) then
    // tail recursion //
     let nopara = nopara.self
     let a2=@(+,preparetail(nopara,self,continue.nopara),empty:seq.block,a)
     let plist = @(+, var, empty:seq.symbol, arithseq(nopara, 1, 1))
     let entry = block("LOOPBLOCK"_1,0,blkno.a2_1,0, plist + Lit(nopara + 1) + loopblock(nopara + 1))
      ascode(p,[entry]+a2)
   else
   ascode(p,a)
   
function   preparetail(nopara:int,self:symbol,continue:symbol,b:block) block
    let code=adjustvar(code.b, nopara, 1, empty:seq.symbol)
    if kind.b="EXIT"_1 &and code_(length.code-1)=self then 
       block("CONTINUE"_1,blkno.b,label1.b,label2.b,subseq(code, 1, length.code-2) + continue ) 
    else block(kind.b,blkno.b,label1.b,label2.b,code)
       
function tailrecursion(self:symbol,b:block) boolean
   kind.b="EXIT"_1 &and (code.b)_(length.code.b-1)=self 
   

function adjustvar(s:seq.symbol, delta:int, i:int, result:seq.symbol)seq.symbol
 if i > length.s then result
 else
  let a = s_i
   if islocal.a then
   adjustvar(s, delta, i + 1, result + var(toint.(fsig.a)_1 + delta))
   else if isdefine.a then
   adjustvar(s, delta, i + 1, result + Define.toword(toint.(fsig.a)_2 + delta))
   else if isloopblock.a then
   let b = subseq(result, 1, i - 2) + Lit(value.s_(i - 1) + delta) + a
     // assert length.b = i report"KLJ"+ toword.length.b + toword.i //
     adjustvar(s, delta, i + 1, b)
   else adjustvar(s, delta, i + 1, result + a)


 function breakblocks(p:program,code:seq.symbol,i:int,start:int,blkcode:seq.symbol,blks:stack.block) seq.block
   if i >  length.code   then 
     [block("FINAL"_1,0,0,0,blkcode+subseq(code,start,i))]
   else 
     if isbr.code_i   then breakblocks(p,code,i+1,i+1,empty:seq.symbol,push(blks,block("BR"_1,i,0,0,blkcode+subseq(code,start,i))))
     else if isexit.code_i  then  breakblocks(p,code,i+1,i+1,empty:seq.symbol,push(blks,block("EXIT"_1,i,0,0,blkcode+subseq(code,start,i))))
     else 
       let rep=code_i
      if not ( module.rep = "$" ) then breakblocks(p,code,i+1,start,blkcode,blks)
      else
       let kind=(fsig.rep)_1
       if kind in "CONTINUE LOOPBLOCK" then 
         breakblocks(p,code,i+1,i+1,empty:seq.symbol,push(blks,block(kind,i,0,0,blkcode+subseq(code,start,i))))
       else  if not(kind  = "BLOCK"_1 ) then breakblocks(p,code,i+1,start,blkcode,blks)
        else  let nopara=toint((fsig.rep)_2)
          let args=top(blks,nopara)
          let subblks=cvtlabels(args,1,empty:seq.block)
          if i=length.code then 
             subblks
          else  if  isexit.code_(i+1)  &and not(kind.subblks_1="LOOPBLOCK"_1 )then
                breakblocks(p,code,i+2,i+2,empty:seq.symbol,push(pop(blks,nopara),
               block("SEQBLKS"_1,blkno.subblks_1,0,0,empty:seq.symbol,subblks)))
          else  if i+3 &le length.code &and isbr.code_(i+3)  &and kind.subblks_1="BR"_1 then
                breakblocks(p,code,i+4,i+4,empty:seq.symbol,push(pop(blks,nopara),
               block("BRBLKS"_1,blkno.subblks_1,0,0,subseq(code,i+1,i+3),subblks))        )
          else 
             breakblocks(p,code,i+1,i+1, blkcode+ascode(p,subblks) ,pop(blks,nopara))
     
 use seq.int
 
 use otherseq.int
 

 
function ascode(p:program,subblks1:seq.block) seq.symbol
ascode(p,subblks1,1,[subblks1_1],empty:seq.symbol) 
  
    
function =(a:block,b:block) boolean blkno.a=blkno.b
  
function   checkforcase(p:program,blk:block) seq.symbol
   if  not.iscaseblock.blk  then empty:seq.symbol
   else 
       let  t = backparse2(code.blk , length.code.blk-5, 1, empty:seq.int)
       let exp=subseq(code.blk,t_1,length.code.blk-5)
        if @(&or,hasstate.p,false,exp) then empty:seq.symbol
        else exp
  
function  ascode(p:program,l:seq.block,i:int,assigned:seq.block,result:seq.symbol) seq.symbol
    if i > length.assigned then result+block.length.assigned else 
    let   blk=assigned_i
    if kind.blk in "BR " then
         let a2=findblk2(l,1,label2.blk)
          let exp=checkforcase(p,blk)
  if   not.isempty.exp  then  
        let r=gathercase(l,blk,exp,empty:seq.caseblock)
            if length.caseblks.r=1   then
              // go ahead and process BR" //
               let c=(caseblks.r)_1
                      let a1=findblk2(l,1,label1.blk)
               let l1=  findindex(a1,assigned)
              let  assigned1=if  l1 > length.assigned then assigned+a1 else assigned
                  let l2=  findindex(a2,assigned1)
                 let  assigned2=if  l2 > length.assigned1 then assigned1+a2 else assigned1 
                  ascode(p,l,i+1,assigned2,result+subseq( code.blk ,1,length.code.blk-5)+keysig.c+EqOp+Lit.l1+Lit.l2+Br)
            else // more than one case block //
              let var=if  islocal.last.exp then last.exp else var.1000
            let prefix=  
            if  islocal.last.exp then subseq((code.blk),1,length.code.blk-6)
          else subseq((code.blk),1,length.code.blk-5) +Define."1000"_1
          let z= rearrangecase( caseblks.r, blkno.last.l+1,  defaultlabel.r,var)
           let newl=  if blkno.last.l  < nextblklabel.z-1 then l+block("?"_1,nextblklabel.z-1,0,0,empty:seq.symbol) else l
         let first= (allocated.z)_1
         let first1=if isempty.prefix then first else  block(kind.first,blkno.first,label1.first,label2.first,
            prefix+code.first) 
         ascode(p,newl,i,replace(assigned,i,first1)+subseq(allocated.z,2,length.allocated.z),result)
     else 
     let a1=findblk2(l,1,label1.blk)
     let l1=  findindex(a1,assigned)
     let  assigned1=if  l1 > length.assigned then assigned+a1 else assigned
      let l2=  findindex(a2,assigned1)
      let  assigned2=if  l2 > length.assigned1 then assigned1+a2 else assigned1 
       ascode(p,l,i+1,assigned2,result+subseq(code.blk,1,length.code.blk-3)+    Lit.l1 + Lit.l2+Br)
    else if kind.blk in "BRC "    then
        let l1=  findindex(label1.blk,1,assigned)
        let assigned1=if l1 > length.assigned then        assigned+findblk2(l,1,label1.blk) else assigned
        let l2=  findindex(label2.blk,1,assigned1)
        let  assigned2=if  l2 > length.assigned1 then  assigned1+findblk2(l,1,label2.blk) else assigned1 
        ascode(p,l,i+1,assigned2,result+subseq(code.blk,1,length.code.blk-3)+    Lit.l1 + Lit.l2+Br)     
    else   if kind.blk in " LOOPBLOCK  " then
     let a1=findblk2(l,1,label1.blk)
     let l1=  findindex(a1,assigned)
     let  assigned1=if  l1 > length.assigned then assigned+a1 else assigned
     ascode(p,l,i+1,assigned1,result+code.blk)
    else
      assert kind.blk in "EXIT CONTINUE" report "PROB 4"+kind.blk
       ascode(p,l,i+1,assigned,result+code.blk)
    
function caseblock(truelabel:int,orgblkno:int,rep:symbol) caseblock
  let key= if module.rep="int $" then toint.(fsig.rep)_1
       else 
         assert module.rep="$word" report "unexpected const type"
         hash.(fsig.rep)_1
  caseblock(key,rep,truelabel,orgblkno)
  
function caseblock(truelabel:int,orgblkno:int,w:word) caseblock
  caseblock(hash.w,Word.w ,truelabel,orgblkno)
  
function findindex(label:int,i:int,a:seq.block) int
   if i > length.a then i else 
  if blkno.a_i=label then i else findindex(label,i+1,a)
 
     
type caseblock is record  key:int,keysig:symbol,truelabel:int,orgblkno:int

function print(c:caseblock) seq.word
"&br"+toword.key.c+print.[keysig.c]+toword.truelabel.c+toword.orgblkno.c

use seq.caseblock

function =(a:caseblock,b:caseblock) boolean  key.a=key.b

function ?(a:caseblock,b:caseblock)  ordering key.a ? key.b

function iscaseblock(blk:block) boolean
   let code=code.blk
   let len=length.code
   len > 5 &and kind.blk="BR"_1  &and     isconst.code_(len-4) &and isinOp.code_(len-3) 
   &and not(module.code_(len-4)="$fref")



        
 type gathercaseresult is record caseblks:seq.caseblock, defaultlabel:int
        
function gathercase(l:seq.block, blk:block,exp:seq.symbol,   caseblks:seq.caseblock )  gathercaseresult
     // blk is a caseblock but have not created the caseblks yet or check for following case blocks //
       let code=code.blk
   let len=length.code
   let label=blkno.findblk2(l,1,label1.blk)
     let t=  if code_(len-3)=EqOp then
       [caseblock(label,blkno.blk,code_(len-4))]
      else 
       let rep= code_(len-4)
       if module.rep="$words" then
           @(+,caseblock(label,0),empty:seq.caseblock, fsig.rep)
       else 
       assert length.constantcode.rep > 2 &and (constantcode.rep)_1=Lit0 report
        "not a standard seq"+print.code
        @(+,caseblock(label,0),empty:seq.caseblock,subseq(constantcode.rep,3,length.constantcode.rep))
// now check to see if following block is a case block //
     let newblock=findblk2(l,1,label2.blk)
     if iscaseblock(newblock) &and subseq(code.newblock,1,length.code.newblock-5)=exp then  gathercase(l,newblock,exp,  caseblks+t )
      else  gathercaseresult(sort(caseblks+t),blkno.newblock) 
      
    
   
     
      
 use otherseq.caseblock   
      
 type     gggresult is record nextblklabel:int,allocated:seq.block  
        
function   rearrangecase( cbs:seq.caseblock, nextblklabel:int,defaultlabel:int,var:symbol) gggresult
        if length.cbs=1 then 
           let blklabel=if orgblkno.cbs_1 > 0 then orgblkno.cbs_1 else nextblklabel
                gggresult(if blklabel=nextblklabel then nextblklabel+1 else nextblklabel,
                     [block("BRC"_1,blklabel,truelabel.cbs_1,defaultlabel,[var,keysig.cbs_1,EqOp,Lit0,Lit0,Br])])
        else if length.cbs=2 then
              let blklabel1=if orgblkno.cbs_1 > 0 then orgblkno.cbs_1 else nextblklabel
              let next1=if blklabel1=nextblklabel then nextblklabel+1 else nextblklabel
              let blklabel2=if orgblkno.cbs_2 > 0 then orgblkno.cbs_2 else next1
               let next2=if blklabel2=next1 then next1+1 else next1
                 gggresult(next2,[block("BRC"_1,blklabel1,truelabel.cbs_1,blklabel2,[var,keysig.cbs_1,EqOp,Lit0,Lit0,Br]),
                       block("BRC"_1,blklabel2,truelabel.cbs_2,defaultlabel,[var,keysig.cbs_2,EqOp,Lit0,Lit0,Br])] )
        else 
         let m=(length.cbs / 2)+1
         let middle=cbs_m
              let low= rearrangecase(subseq(cbs,1,m-1),nextblklabel+2,defaultlabel,var) 
              let high=rearrangecase(subseq(cbs,m +1,length.cbs),nextblklabel.low,defaultlabel,var) 
              let lowerlabel=  blkno.(allocated.low )_1
              let upperlabel=  blkno.(allocated.high )_1
               gggresult(nextblklabel.high,  
               [ block("BRC"_1,nextblklabel,upperlabel,nextblklabel+1,[var,keysig.middle,gtOp,Lit0,Lit0,Br]),
               block("BRC"_1,nextblklabel+1,truelabel.middle,lowerlabel,[var,keysig.middle,EqOp,Lit0,Lit0,Br])]
               +allocated.low+allocated.high)
               
       
      
        
    

use otherseq.block            
           
    
function findblk2( l:seq.block,i:int,blkno:int) block
     assert  i &le length.l report "did not find block"   
      let blk=l_i
      if   blkno.blk=blkno then 
        if kind.blk="JMP"_1 then  findblk2(l,1,label1.blk)  else blk
    else findblk2(l,i+1,blkno)  
       
function  ascode( r:set.int,t:block) seq.symbol
          if not(blkno.t in r ) then empty:seq.symbol
          else  if  kind.t="BR"_1 then
                subseq(code.t,1,length.code.t-3)+
              Lit.findindex(label1.t,toseq.r) + Lit.findindex(label2.t,toseq.r)+Br
         else  
           assert kind.t in "EXIT CONTINUE LOOPBLOCK" report "PROB 4"+kind.t
           code.t

 function cvtlabels( blks:seq.block,i:int,result:seq.block)seq.block
    // set block labels in BR //
            if i > length.blks then 
               let b=blks_1
              if kind.b="LOOPBLOCK"_1 then
                let label=blkno.blks_2
                 [block("LOOPBLOCK"_1,blkno.b,label,label,code.b)]+subseq(result,2,length.result)
              else
              result else
              let b=blks_i
             let newtrees= if  kind.b="BR"_1 &and label1.b=0 then
                       let len=length.code.b
                     [ block(kind.b,blkno.b,blkno.blks_value.(code.b)_(len-2),
                                                blkno.blks_value.(code.b)_(len-1),code.b) ]
              else if kind.b="SEQBLKS"_1 then  
                 subblks.blks_i 
              else if kind.b="BRBLKS"_1 then
                   assert length.code.b=3 report "OPT P"
                   @(+,  convertexits(blkno.blks_value.(code.b)_1,blkno.blks_value.(code.b)_2),  
                   empty:seq.block,subblks.b)
               else [blks_i ]
              cvtlabels(blks,i+1,result+newtrees)
              
        
function       print(b:block) seq.word
     "&br >>>>"+[kind.b,toword.blkno.b]+if kind.b in "BR BRC" then [toword.label1.b,toword.label2.b ] 
      +print.//[(code.b)_(length.code.b-3)]// code.b 
     else if kind.b="BRBLKS"_1 then "("+@(+,print,"",subblks.b)+")"
     else if kind.b in "EXIT CONTINUE"  then print.code.b
     else  if kind.b="JMP"_1 then [ toword.label1.b ]+print.code.b else "??"
     
          
              
function convertexits(    label1:int,label2:int,  b:block) block
             if kind.b in "BR JMP"  then b
             else assert kind.b="EXIT"_1 report "unexpected block type"+kind.b
                  if length.code.b=2 &and isconst.(code.b)_1  
                 then      let target=if Lit0  =(code.b)_1 then label2 else label1
                    block("JMP"_1,blkno.b,target,target,empty:seq.symbol) 
         else 
                   block("BR"_1,blkno.b,label1,label2, subseq(code.b,1,length.code.b-1)+[Lit0,Lit0,Br])
             
            
      

use UTF8

use bits

use seq.char



use otherseq.seq.int

use seq.seq.int

use seq.int

use set.int

use seq.mytype

use real




use blockseq.seq.symbol

use worddict.seq.symbol


use seq.seq.seq.symbol

use seq.seq.symbol

use seq.symbol

use set.symbol

use stacktrace

use stdlib

use otherseq.word

use seq.seq.word

use seq.word

use set.word

use libdesc

use set.seq.word

use seq.symbol

use symbol

use seq.firstpass

use set.symbol



 Function pass2(   placehold:program,compiled:set.symbol
 ,roots:seq.symbol,mods:seq.firstpass,templates:program,exports:seq.word) intercode
    let p = @( depthfirst(placehold),identity,emptyprogram,toseq.toset.placehold)
      let libmods=libdesc(p, templates,mods,exports,roots )
    let t=uses(p,empty:set.symbol,asset.roots+libmods)
    let defines2=@(+, defines2(p),empty:seq.symbol,toseq.(t-compiled )) 
    intercode( defines2,t,p,libmods)
  
 
     
     
      
function  uses(p:program,s:symbol) seq.symbol
    let d=code.lookupcode(p,s)
    if isempty.d then 
      constantcode.s
    else d
         
function   uses(p:program,processed:set.symbol, toprocess:set.symbol) set.symbol
   if isempty.toprocess then  processed else 
    let q= asset.@(+,uses.p,empty:seq.symbol,     toseq.toprocess)
      uses(p,processed &cup toprocess, q-processed)


function defines2(p:program,s:symbol) seq.symbol
if isconst.s  &or module.s in ["$","builtin","local","$fref","$constant"]  &or  isabstract.mytype.module.s 
then empty:seq.symbol 
else 
let d=code.lookupcode(p,s)
    if isempty.d then empty:seq.symbol
    else [s]



type backresult is record code:seq.symbol, places:seq.int

use process.seq.symbol
  
Function firstopt(p:program, rep:symbol, code:seq.symbol) program
 let nopara=nopara.rep
 if module.rep="builtin" then
  let options= caloptions(p,code,nopara,module.rep,fsig.rep)
  map(p,symbol(fsig.rep,module.rep,returntype.rep), addoptions(code,options)) 
 else 
 let pdict=addpara(emptyworddict:worddict.seq.symbol, nopara)
 let t=deepcopy.code
 let code2 = code.yyy(p,t,1, t, 1, nopara + 1, pdict)
  let options= caloptions(p,code2,nopara,module.rep,fsig.rep)
  let s=symbol (fsig.rep,module.rep,returntype.rep )
 let a = breakblocks(p,code2,s)
 let a2=code.yyy(p,a,1,a,1,nopara+1,pdict)
  map(p, s, addoptions(a2,options)) 
   
   use process.int
   
   use seq.symbol
   
   use set.symbol
    
function print(s:seq.int)seq.word @(+, toword,"", s)


function var(i:int) symbol var.toword.i

function var(w:word) symbol  Local.w



function addpara(map:worddict.seq.symbol, i:int)worddict.seq.symbol
 if i ≤ 0 then map
 else
  let v = var.i
   addpara(add(map, toword.i, [ v]), i - 1)

function addlooplocals(map:worddict.seq.symbol, firstvar:int, nextvar:int, nopara:int, i:int)worddict.seq.symbol
 if i = nopara then map
 else
  addlooplocals(replace(map, toword.(firstvar + i), [ var(nextvar + i)]), firstvar, nextvar, nopara, i + 1)
  
function yyy(p:program,org:seq.symbol,k:int, s:seq.symbol, i:int, nextvar:int, map:worddict.seq.symbol)expandresult
 if i > length.s then expandresult(nextvar, s)
 else let sym=org_k
 //  assert   sym=org_k report "DIFF"+print.subseq(s,1 ,i-1)+"!"+print.subseq(s,i ,length.s) 
 +"&br ----------- &br"+  print.subseq(org,1 ,k-1)+"!"+                                  print.subseq(org,k ,length.org) 
 +stacktrace  //
 if module.sym in ["$constant","$fref","$word","$words","int $"] then yyy(p,org,k+1, s, i + 1, nextvar, map)
 else
   if  module.sym="local" then 
      let t = lookup(map, (fsig.sym)_1)
      if isempty.t then yyy(p,org,k+1, s, i + 1, nextvar, map)
       else yyy(p,org,k+1, replace(s, i, 1, t_1), i + length.t_1, nextvar, map)
  else  if last.module.sym="$"_1 then 
      if  fsig.sym="BLOCK 3" then
     let t = backparse(s, i - 1, 3, empty:seq.int) + i
     let condidx=t_2-4
     let cond=s_ condidx
     if   isbr.s_( condidx+3)   &and isconst(cond) then
        let keepblock=if value.cond=1 then value.s_(condidx+1) else value.s_(condidx+2)
        let new=subseq(s,t_keepblock,t_(keepblock+1)-2)
        yyy(p,org,k+1, replace(s, condidx, i-condidx+1, new), condidx+length.new, nextvar, map) 
     else    yyy(p,org,k+1, s, i + 1, nextvar, map)
   else  if (fsig.sym)_1="BR"_1   then
       if (fsig.sym)_2="3"_1 &and s_(i-3)=notOp then
          yyy(p,org,k+1,replace(s,i-3,3,[s_(i-1),s_(i-2)]),i,nextvar,map)
      else yyy(p,org,k+1, s, i + 1, nextvar, map)
   else if // isdefine //  (fsig.sym)_1="DEFINE"_1  then
      let thelocal=(fsig.sym)_2
      if i > 1 ∧ (isconst.s_(i - 1) ∨ islocal.s_(i - 1))then
         yyy(p,org,k+1, replace(s, i - 1, 2, empty:seq.symbol), i - 1, nextvar, replace(map, thelocal, [ s_(i - 1)]))
       else
         yyy(p,org,k+1, replace(s, i, 1, [ Define.toword.nextvar]), i + 1, nextvar + 1, replace(map, thelocal, [ var.nextvar]))
   else if  (fsig.sym)_1="LOOPBLOCK"_1 then
      let nopara = toint.(fsig.sym)_2 - 1
      let firstvar = value.s_(i - 1)
      yyy(p,org,k+1, replace(s, i - 1, 1, [ Lit.nextvar]), i + 1, nextvar + nopara, addlooplocals(map, firstvar, nextvar, nopara, 0))
   else if (fsig.sym)_1="RECORD"_1 then
      let nopara = toint.(fsig.sym)_2
      let args = subseq(s, i - nopara, i - 1)
      if @(∧, isconst, true, args) then
        yyy(p,org,k+1, replace(s, i - nopara, nopara + 1, [ constant.args]), i - nopara+1, nextvar, map)
      else yyy(p,org,k+1, s, i + 1, nextvar, map)
   else if  (fsig.sym)_1="APPLY"_1 then
       applycode(p,org,k, nextvar, s, i,map)
   else if  (module.sym)_1="para"_1   then  
      let sym2=Local.(module.sym)_2
       let t = lookup(map, (fsig.sym2)_1)
       if isempty.t then yyy(p,org,k+1, replace(s,i,1,[sym2]), i + 1, nextvar, map)
        else yyy(p,org,k+1, replace(s, i, 1, t_1), i + length.t_1, nextvar, map)
     else  yyy(p,org,k+1, s, i + 1, nextvar, map)
  else     
     let nopara= nopara.sym 
     let dd=code.lookupcode(p, sym)
    if not.isempty.dd &and "INLINE"_1 in options.dd then
         let code =   if (last.dd=Optionsym) then subseq(dd,1,length.dd-2) else   dd
         if isempty.code then yyy(p,org,k+1, s, i + 1, nextvar, map)
         else
      inline(p,org,k, s, i, nextvar,nopara,code,map)
 else if nopara=0 &or nopara > 2 &or not(isconst.s_(i - 1)) then yyy(p,org,k+1, s, i + 1, nextvar, map)
 else if  not(module.sym in ["builtin","char seq encoding","word seq","int seq","UTF8",
 " char seq erecord","words"])  &and not(last.module.sym="seq"_1)  
   then yyy(p,org,k+1, s, i + 1, nextvar, map)
 else 
  // one or two parameters with last arg being constant //
 if nopara = 1 then optoneop(p,org,k, s, i , nextvar, map,sym)
 else // should add case of IDXUC with record as first arg //
   if fsig.sym in[ "decode(T erecord, T encoding)","decode(char seq erecord, char seq encoding)"] ∧ s_(i - 2) = wordEncodingOp  
 &and module.sym="char seq encoding" then
  let arg1 =s_(i - 1)
   if module.arg1 = "$word"then
   let a1 = @(+, Lit, empty:seq.symbol, tointseq.decodeword.(fsig.arg1)_1)
    let d = constant.([ Lit.0, Lit.length.a1] + a1)  
     yyy(p,org,k+1, replace(s, i - 2, 3, [d]), i + 1- 2, nextvar, map)
   else yyy(p,org,k+1, s, i + 1, nextvar, map)
  else if fsig.sym in[ "encode(T erecord,T)","encode(char seq erecord, char seq)"] ∧ s_(i - 2) = wordEncodingOp  
    &and module.sym="char seq encoding" then
  let arg1 = s_(i - 1)
   if module.arg1 = "$constant"then
      let chseq=  @(+,  value,empty:seq.int,subseq(constantcode.arg1,3,length.constantcode.arg1))
        assert  @(&and, islit,true,  subseq(constantcode.arg1,3,length.constantcode.arg1)) report "const problem" 
       let new=   Word.encodeword.@(+,char,empty:seq.char,chseq)
      yyy(p,org,k+1, replace(s, i - 2, 3, [new]), i - 1, nextvar, map)
   else yyy(p,org,k+1, s, i + 1, nextvar, map)
 else if not.isconst.s_(i - 2) then  yyy(p,org,k+1, s, i + 1, nextvar, map)
 else  
  //  two parameters with   constant  args //
   if module.sym="builtin" then opttwoopbuiltin(p,org,k, s, i , nextvar, map,sym)
   else  
     if   last.module.sym="seq"_1 &and 
       (fsig.sym="_(T seq,int)" &or fsig.sym=
           "_("+subseq(module.sym,1,length.module.sym-1)+"seq,int)" )then
      let idx = value.s_(i - 1)
      let arg1 =  s_(i - 2)
    if module.arg1 = "$words" &and  between(idx, 1, length.fsig.arg1) then
      yyy(p,org,k+1, replace(s, i - 2, 3, [ Word.(fsig.arg1)_idx]), i - 1, nextvar, map)
   else if    module.arg1 = "$constant" &and  between(idx, 1, length.constantcode.arg1-2) then
      yyy(p,org,k+1, replace(s, i - 2, 3, [ (constantcode.arg1)_(idx+2)]), i - 1, nextvar, map)
   else yyy(p,org,k+1, s, i + 1, nextvar, map)
 else   if  fsig.sym in ["+(T seq, T seq)","+(word seq, word seq)"] &and module.sym="word seq" then
 let arg1 =  s_(i - 2)
  let arg2 =  s_(i - 1)
   if module.arg1 = "$words" ∧ module.arg2 = "$words"then
     yyy(p,org,k+1, replace(s, i - 2, 3, [ Words(fsig.arg1 + fsig.arg2)]), i - 1, nextvar, map)
   else yyy(p,org,k+1, s, i + 1, nextvar, map)
 else yyy(p,org,k+1, s, i + 1, nextvar, map)
 
function optoneop(p:program,org:seq.symbol,k:int, s:seq.symbol, i:int, nextvar:int, map:worddict.seq.symbol,rep:symbol)expandresult
 if fsig.rep = "makereal(word seq)" &and module.rep="UTF8" then
 let arg1 =  s_(i - 1)
   if module.arg1 = "$words"then
   let  x=Lit.representation.makereal.fsig.arg1 
     yyy(p,org,k+1, replace(s, i - 1, 2, [ x]), i, nextvar, map)
   else yyy(p,org,k+1, s, i + 1, nextvar, map)
 else if fsig.rep = "merge(word seq)" &and module.rep="words" then
 let arg1 =  s_(i - 1)
   if module.arg1 = "$words"then
     yyy(p,org,k+1, replace(s, i - 1, 2, [ Word.merge.fsig.arg1 ]), i, nextvar, map)
   else yyy(p,org,k+1, s, i + 1, nextvar, map)
else yyy(p,org,k+1, s, i + 1, nextvar, map)

function opttwoopbuiltin(p:program,org:seq.symbol,k:int, s:seq.symbol, i:int, nextvar:int, map:worddict.seq.symbol,rep:symbol)expandresult
 if fsig.rep  =" IDXUC(int,int)"   then
    let j = value.s_(i - 1)
    let x =  s_(i - 2)
    if between(j, 0, length.constantcode.x - 1)then
      yyy(p,org,k+1, replace(s, i - 2, 3, [(constantcode.x)_(j + 1)]), i - 1, nextvar, map)
    else yyy(p,org,k+1, s, i + 1, nextvar, map)
 else  if fsig.rep = "+(int,int)" then 
   if module.s_(i - 2)="$constant" then // address calculation //
     yyy(p,org,k+1, s, i + 1, nextvar, map)
   else 
   let new= replace(s, i - 2, 3, [ Lit(value.s_(i - 2) + value.s_(i - 1))])
   yyy(p,org,k+1,new,i-1,nextvar,map)
 else if fsig.rep="*(int,int)" then
   let new=replace(s, i - 2, 3, [ Lit(value.s_(i - 2) * value.s_(i - 1))])
    yyy(p,org,k+1,new,i-1,nextvar,map)
 else if fsig.rep="-(int,int)" then
   let new= replace(s, i - 2, 3, [ Lit(value.s_(i - 2) - value.s_(i - 1))])
   yyy(p,org,k+1,new,i-1,nextvar,map)
 else if fsig.rep="/(int,int)" ∧ value.s_(i - 1) ≠ 0 then
  let new=replace(s, i - 2, 3, [ Lit(value.s_(i - 2) / value.s_(i - 1))])
   yyy(p,org,k+1, new, i - 1 , nextvar , map)
 else if fsig.rep="=(int,int)"  then
   let new=replace(s, i - 2, 3, [ if  s_(i - 2) =  s_(i - 1)  then Lit.1 else Lit.0])
  yyy(p,org,k+1,new,i-1,nextvar,map)
 else if fsig.rep=">(int,int)"  then
   let new=replace(s, i - 2, 3, [ if value.s_(i - 2) > value.s_(i - 1)  then Lit.1 else Lit.0])
  yyy(p,org,k+1,new,i-1,nextvar,map)
   else if fsig.rep="∨ (bits, bits)" then
  let new=replace(s, i - 2, 3, [ Lit.toint(bits.value.s_(i - 2) &or bits.value.s_(i - 1))])
  yyy(p,org,k+1,new,i-1,nextvar,map)
  else if fsig.rep="∧ (bits, bits)" then
  let new=replace(s, i - 2, 3, [ Lit.toint(bits.value.s_(i - 2) &and bits.value.s_(i - 1))])
  yyy(p,org,k+1,new,i-1,nextvar,map)
 else if fsig.rep="<<(bits, int)" then
  let new=replace(s, i - 2, 3, [ Lit.toint(bits.value.s_(i - 2) << value.s_(i - 1))])
  yyy(p,org,k+1,new,i-1,nextvar,map)
 else if  fsig.rep=">>(bits, int)"then
  let new=replace(s, i - 2, 3, [ Lit.toint(bits.value.s_(i - 2) >> value.s_(i - 1))])
  yyy(p,org,k+1,new,i-1,nextvar,map)
 else if fsig.rep="-(real,real)" then 
  let new= replace(s, i - 2, 3, [ Lit.representation(casttoreal.value.s_(i - 2) - casttoreal.value.s_(i - 1))])
  yyy(p,org,k+1,new,i-1,nextvar,map)
  else yyy(p,org,k+1, s, i + 1, nextvar, map)
  


 
 
function islit(s:symbol) boolean   module.s ="int $" 


 function inline(p:program,org:seq.symbol,k:int, s:seq.symbol, i:int, nextvar:int,nopara:int,code:seq.symbol, map:worddict.seq.symbol)
  expandresult
      if length.code = 1 ∧ code = [ var.1]then
   // function just returns result // 
       yyy(p,org,k+1,replace(s, i, 1, empty:seq.symbol),i,nextvar,map)
    else
    let t = backparse(s, i - 1, nopara, empty:seq.int) + i
     assert length.t = nopara + 1 report"INLINE PARA" + print.subseq(s, 1, i)
     let new = if issimple(p,nopara,code) then 
         let pmap=simpleparamap(s, t, emptyworddict:worddict.seq.symbol, nopara)
         code.yyy(p,code,1, code, 1, nextvar, pmap)
    else 
          expandinline(s, t, emptyworddict:worddict.seq.symbol, nopara, empty:seq.symbol, nextvar, code, p)
       yyy(p,org,k+1, replace(s, t_1, i - t_1 + 1, new),t_1 + length.new,nextvar + nopara,map)
         
   function simpleparamap(s:seq.symbol,t:seq.int,pmap:  worddict.seq.symbol,i:int)  worddict.seq.symbol
     if i=0 then pmap else 
       simpleparamap(s, t, add(pmap, toword.i, subseq(s, t_i, t_(i + 1) - 1)), i - 1)

function expandinline(s:seq.symbol, t:seq.int, pmap: worddict.seq.symbol, i:int, newcode:seq.symbol, nextvar:int, inlinecode:seq.symbol, p:program)seq.symbol
 // when i > 0 then assigning parameters to new local variables //
 if i = 0 then newcode+code.yyy(p,inlinecode,1, inlinecode, 1, nextvar, pmap)
 else
  expandinline(s, t, add(pmap, toword.i, [ var.nextvar]), i - 1, 
  subseq(s, t_i, t_(i + 1) - 1) + Define.toword.nextvar +newcode, nextvar + 1, inlinecode, p)

function backparse(s:seq.symbol, i:int, no:int, result:seq.int)seq.int
 if no = 0 then result
 else
  assert i > 0 report"back parse 1:" + toword.no+print.s+stacktrace
   assert not.isdefine.s_i report"back parse 2" + print.s
   let nopara = nopara.s_i
    // if nopara = 0 then assert i = 1 &or not.isdefine.s_(i - 1)report"back parse 2a"+ print.s backparse(s, i - 1, no - 1, [ i]+ result)else //
    let first = if nopara = 0 then i
    else
     let args = backparse(s, i - 1, nopara, empty:seq.int)
      assert length.args = nopara report"back parse 3" + print.[ s_i] + toword.nopara + "//"
      + @(+, toword,"", args)
       args_1
    let b = if first > 1 ∧ isdefine.s_(first - 1)then
    let c = backparse(s, first - 2, 1, empty:seq.int)
      c_1
    else first
     backparse(s, b - 1, no - 1, [ b] + result)
     
function backparse2(s:seq.symbol, i:int, no:int, result:seq.int)seq.int
 if no = 0 then result
 else
  assert i > 0 report"back parse 1" + toword.no+print.s
   assert not.isdefine.s_i report"back parse 2x" + print.s
   let nopara = nopara.s_i
    let first = if nopara = 0 then i
    else
     let args = backparse(s, i - 1, nopara, empty:seq.int)
      assert length.args = nopara report"back parse 3" + print.[ s_i] + toword.nopara + "//"
      + @(+, toword,"", args)
       args_1
    let b = first
     backparse2(s, b - 1, no - 1, [ b] + result)

function replace(s:seq.symbol, start:int, length:int, value:seq.symbol)seq.symbol
 subseq(s, 1, start - 1) + value + subseq(s, start + length, length.s)

function adddefines2(s:seq.symbol, t:seq.int, i:int, nopara:int, newcode:seq.symbol, nextvar:int)seq.symbol
 if i > nopara then newcode
 else
  adddefines2(s, t, i + 1, nopara, newcode + subseq(s, t_i, t_(i + 1) - 1)
  + Define.toword(nextvar + i - 1), nextvar)

type expandresult is record nextvar:int,  code:seq.symbol

function applycode(p:program,org:seq.symbol,k:int, nextvar:int, code:seq.symbol, index:int,map:worddict.seq.symbol)  expandresult
 let pseq = code_(index - 1)
 let term1 = constantcode.code_(index - 2)
 let term2 = constantcode.code_(index - 3)
 let nopara1 = nopara.term1_1 - 2
 let nopara2 = nopara.term2_1 - 1
 let allpara = @(+, var, empty:seq.symbol, arithseq(nopara1 + nopara2 + 2, 1, nextvar))
 let map1 = add(emptyworddict:worddict.seq.symbol,  "term1para"_1, subseq(allpara, 1, nopara1))
 let map2 = add(map1,  "term2para"_1, subseq(allpara, nopara1 + 1, nopara1 + nopara2))
 let map3 = add(map2,  "term1"_1, term1)
 let map4 = add(map3,  "term2"_1, term2)
 let map5 = add(map4, "FREFpseq"_1, [ pseq])
 let t = backparse(code, index - 4, nopara1 + nopara2 + 2, empty:seq.int)
 let noop = nopara1 + nopara2 = 0 ∧ checknoop(p,term2) ∧ t_2 - t_1 = 1
 ∧ code_(t_1) = emptyseqOp ∧ checkcat( term1_1 )
 ∧ not((fsig.term2_1)_1 = "deepcopy"_1)
  if noop then
   let new = subseq(code, 1, t_1 - 1) + subseq(code, t_2, index - 4)
  // assert not(subseq(code, t_2, index - 4)=[var.1]) report "XXXX"+print.code+"/new/"+print.new //
     let a=new + subseq(code, index + 1, length.code)
     yyy(p,org,k+1, a,length.new + 1,nextvar,map)
  else
   let paras = adddefines2(code, t + (index - 3), 1, nopara1 + nopara2 + 2, empty:seq.symbol, nextvar)
   let a=applytemplate
   let body = yyy(p,a,1, a, 1, nextvar + nopara1 + nopara2 + 2, map5)
   let new = paras + subseq(allpara, nopara1 + nopara2 + 1, length.allpara) + code.body
    // assert false report"APPLY"+ print.new +"
&p"+ print.code +"
&p"+ print.t +"<"+ toword(nopara1 + nopara2 + 2)//
yyy(p,org,k+1, replace(code, t_1, index - t_1 + 1, new), t_1 + length.new, nextvar.body, map)
  
function checknoop(p:program,dd:seq.symbol)boolean
 let s =     if length.dd > 2 &and (last.dd=Optionsym) then subseq(dd,1,length.dd-2) else   dd
 if length.s ≠ 1 then false
 else if s_1 = var.1 then true
 else
    checknoop(p,code.lookupcode(p,s_1) ) 
    
  
function checkcat(f:symbol) boolean
 let p=subseq(module.f,1,length.module.f-1)
  last.module.f = "seq"_1
 ∧   fsig.f = "+("+p+  "seq,"+p+")"

function applytemplate seq.symbol
let CALLIDX =symbol("callidx(int,T seq,int)","builtin", "?")
let STKRECORD= symbol("STKRECORD(int,int)","builtin", "?")
let theseq = 5
let stk = 6
 [ Lit.0, Lit.4, loopblock.4, var.theseq, Lit.0, IDXUC, var."FREFpseq"_1, EqOp, Lit.3, Lit.4
 , Br, var.4, var.theseq, Lit.2, IDXUC, var.stk, var.theseq, Lit.3, IDXUC, STKRECORD
 , continue.3, var.theseq, Lit.1, IDXUC, Define."8"_1, var.4, Lit.1, Lit.9, loopblock.3, var.10
 , var.8, gtOp, Lit.3, Lit.4, Br, var.9, Exit, var."term2para"_1, var.theseq, Lit.0
 , IDXUC, Lit.0, EqOp, Lit.2, Lit.3, Br, var.theseq, var.10, Lit.1, PlusOp
 , IDXUC, Exit, var.theseq, Lit.0, IDXUC, var.theseq, var.10, CALLIDX, Exit, block.3
 , var."term2"_1, Define."11"_1, var."term1para"_1, var.9, var.11, var."term1"_1, var.10, Lit.1, PlusOp, continue.2
 , block.4, Define."7"_1, var.stk, Lit.0, EqOp, Lit.5, Lit.6, Br, var.7, Exit
 , var.7, var.stk, Lit.1, IDXUC, var.stk, Lit.0, IDXUC, continue.3, block.6]


  

function depthfirst(knownsymbols:program,processed:program,s:symbol) program
        depthfirst(knownsymbols,1,[s],processed,code.lookupcode(knownsymbols,s),s)



     
function     depthfirst(knownsymbols:program,i:int,pending:seq.symbol,processed:program,code:seq.symbol,s:symbol) program
        if i > length.code then
                 firstopt(processed,s, code )
        else 
         let sym=code_i
     let newprg=     if  isnocall.sym  then processed
    else 
      let sym2=if module.sym="$fref" then     (zcode.sym)_1 else sym
      if   sym2 in pending then   processed  
      else      let r= lookupcode(processed,sym)
              if isdefined.r then processed
             else 
               let rep2=  lookupcode(knownsymbols,  sym2) 
              if  length.code.rep2  > 0 then 
                depthfirst(knownsymbols, 1,pending+sym2,processed,code.rep2 ,sym2)
              else processed
        depthfirst(knownsymbols,   i +  1, pending, newprg,code,s)





type intercode is record   defines:seq.symbol, uses:set.symbol,theprg:program,libdesc:symbol
  
Function  intercode (defines:seq.symbol,  uses:set.symbol,p:program,libdesc:symbol) intercode export
   
Function uses(i:intercode)set.symbol  export
 
Function theprg(intercode) program export

Function defines(i:intercode)seq.symbol  export

Function libdesc(i:intercode) symbol  export

function astext(f:symbol)seq.word
 let module=module.f 
let fsig=fsig.f
if  module="local" then [ merge.(["%"_1]+fsig)]
   else if  module="int $"  then fsig
   else if module="$words" then '"' + fsig + '"'
   else if module="$word" then "WORD"+fsig
    else if module ="$" then 
   if fsig_1 in "BLOCK EXITBLOCK BR LOOPBLOCK FINISHLOOP CONTINUE"then fsig + " &br"else fsig
   else if module=" $constant"  then fsig 
   else if module in ["$fref"] then "FREF"+mangledname.(constantcode.f)_1
   else if last.module ="para"_1 then "LOCAL"+fsig+(module.f)_1
   else [mangledname.f]
 
function ithfunc(p:program, i:symbol)seq.word
 let d=lookupcode(p,i) if not.isdefined.d then astext(i) else
 astext(i)+ @(+, astext,"",code.d ) 

Function print(a:intercode)seq.seq.word  
@(+, ithfunc.theprg.a,empty:seq.seq.word, defines.a)


________________________________

 

Function addoptions(code:seq.symbol,options:seq.word) seq.symbol
 if options ="" then code
 else  
  let codewithoutoptions= if length.code > 0 &and  last.code=Optionsym then subseq(code,1,length.code-2) else code
    codewithoutoptions+Words.options+Optionsym


          
Function   caloptions(p:program,code:seq.symbol,nopara:int,modname:seq.word,fsig:seq.word) seq.word
           let options= options.code  
         if length.code=0 then if  not(modname="builtin" ) then  "STATE" else ""
         else if fsig="in(int, int seq)" &or  fsig="in(word, word seq)" 
         &or  fsig="_(int seq, int)"   &or  fsig="_(word seq, int)" then ""   
         else
           let codeonly= if   last.code=Optionsym then subseq(code,1,length.code-2) else code
             let newoptions =options+if not("STATE"_1 in options) &and  @(&or,hasstate.p,false  ,codeonly ) then "STATE" else ""
        newoptions+if  "NOINLINE"_1 in options &or length.code > 20 &or checkself(fsig,modname,codeonly)  then
        ""  else    "INLINE" 
        
               
function checkself(fsig:seq.word,module:seq.word,s:symbol) boolean
    fsig=fsig.s &and module=module.s
    
function checkself(fsig:seq.word,module:seq.word,s:seq.symbol) boolean
@(&or,checkself(fsig,module),false,s)

Function print(s:seq.symbol)seq.word @(+, print,"", s)

Function loopblock(i:int)symbol  symbol([ "LOOPBLOCK"_1,toword.i],   "$",  "?")

Function continue(i:int)symbol   symbol([ "CONTINUE"_1,toword.i],    "$",   "?")

Function block(i:int)symbol  symbol([ "BLOCK"_1,toword.i],  "$",   "?")


Function isblock(s:symbol)boolean module.s  = "$" ∧ (fsig.s)_1="BLOCK"_1 

Function isrecord(s:symbol)boolean module.s  = "$" ∧ (fsig.s)_1="RECORD"_1

Function isapply(s:symbol)boolean  module.s  = "$" ∧ (fsig.s)_1="APPLY"_1

Function isloopblock(s:symbol)boolean module.s  = "$" ∧ (fsig.s)_1="LOOPBLOCK"_1

Function isdefine(s:symbol)boolean  module.s  = "$" ∧ (fsig.s)_1="DEFINE"_1

Function isexit(s:symbol)boolean module.s =  "$" ∧  fsig.s ="EXITBLOCK 1"

Function isbr(s:symbol)boolean module.s =  "$" ∧  fsig.s ="BR 3"
 
Function notOp symbol symbol("not(boolean)","builtin","boolean")

Function wordEncodingOp symbol symbol("wordencoding","words", " char seq erecord")

Function emptyseqOp symbol   constant.[ Lit0, Lit0]

Function gtOp symbol   symbol(">(int, int)","builtin", "boolean")
 

  // statebit is set on option so that adding an option doesn't auto add a inline bit //
 
 
Function issimple(p:program,nopara:int, code:seq.symbol)boolean
    between(length.code, 1, 15)  
 ∧ (nopara = 0 ∨ checksimple(p,code, 1, nopara, 0))
 
Function hasstate(p:program,s:symbol) boolean 
if module.s in ["int $","$word","$words","$","$fref","local","$constant"] then false else
if ( fsig.s=  "_(int seq, int)" &or fsig.s= "_(word seq,int)") then false else
let d=lookupcode(p,s)
 if  isdefined.d then "STATE"_1 in options.code.d else not(module.s="builtin")


function checksimple(p:program,code:seq.symbol, i:int, nopara:int, last:int)boolean
 // check that the parameters occur in order and they occur only once //
 // encodings of first 8 parameters is such that the encoding equals the parameter no. //
 // any op that may involve state must occur after all parameters //
 if i > length.code then true
 else
  if  nopara < last &and // should also check for loopblock // hasstate(p,code_i) then 
   // state op between parameters //
   false
   else
     let rep= code_i
     if module.rep="local" then
       let parano=toint.(fsig.rep)_1 
       if parano=last+1 then checksimple(p,code, i + 1, nopara, last + 1) else false
      else checksimple(p,code, i + 1, nopara, last)
