

Module pass2new

run mylib testnew 

run mylib test

type block is record kind:word,blkno:int,label1:int,label2:int,code:seq.sig,subblks:seq.block


function block(kind:word,blkno:int,label1:int,label2:int,code:seq.sig) block
  block(kind,blkno,label1,label2,code,empty:seq.block)

use seq.block

use stack.block


function breakblocks(code:seq.sig,self:sig) seq.sig  
  let a=breakblocks(code,1,1,empty:seq.sig,empty:stack.block)
  if length.a=1 then code.a_1 else 
   if not(kind.a_1="LOOPBLOCK"_1) &and @(&or,tailrecursion.self,false,a) then
    // tail recursion //
     let nopara = noparafsignrep.decode.self
     let a2=@(+,preparetail(nopara,self,continue.nopara),empty:seq.block,a)
     let plist = @(+, var, empty:seq.sig, arithseq(nopara, 1, 1))
     let entry = block("LOOPBLOCK"_1,0,blkno.a2_1,0, plist + lit(nopara + 1) + loopblock(nopara + 1))
      ascode([entry]+a2)
   else
   ascode.a
   
function   preparetail(nopara:int,self:sig,continue:sig,b:block) block
    let code=adjustvar(code.b, nopara, 1, empty:seq.sig)
    if kind.b="EXIT"_1 &and code_(length.code-1)=self then 
       block("CONTINUE"_1,blkno.b,label1.b,label2.b,subseq(code, 1, length.code-2) + continue ) 
    else block(kind.b,blkno.b,label1.b,label2.b,code)
       
function tailrecursion(self:sig,b:block) boolean
   kind.b="EXIT"_1 &and (code.b)_(length.code.b-1)=self 
   

function adjustvar(s:seq.sig, delta:int, i:int, result:seq.sig)seq.sig
 if i > length.s then result
 else
  let a = s_i
   if islocal.a then
   adjustvar(s, delta, i + 1, result + var(toint.(fsig.decode.a)_1 + delta))
   else if isdefine.a then
   adjustvar(s, delta, i + 1, result + define.toword(toint.(fsig.decode.a)_2 + delta))
   else if isloopblock.a then
   let b = subseq(result, 1, i - 2) + lit(value.s_(i - 1) + delta) + a
     // assert length.b = i report"KLJ"+ toword.length.b + toword.i //
     adjustvar(s, delta, i + 1, b)
   else adjustvar(s, delta, i + 1, result + a)


 function breakblocks(code:seq.sig,i:int,start:int,blkcode:seq.sig,blks:stack.block) seq.block
   if i >  length.code   then 
     [block("FINAL"_1,0,0,0,blkcode+subseq(code,start,i))]
   else 
     if code_i =br then breakblocks(code,i+1,i+1,empty:seq.sig,push(blks,block("BR"_1,i,0,0,blkcode+subseq(code,start,i))))
     else if code_i=exit then  breakblocks(code,i+1,i+1,empty:seq.sig,push(blks,block("EXIT"_1,i,0,0,blkcode+subseq(code,start,i))))
     else if not.lookcloser.code_i then breakblocks(code,i+1,start,blkcode,blks)
     else
       let rep=decode.code_i
      if not ( module.rep = "$" ) then breakblocks(code,i+1,start,blkcode,blks)
      else
       let kind=(fsig.rep)_1
       if kind in "CONTINUE LOOPBLOCK" then 
         breakblocks(code,i+1,i+1,empty:seq.sig,push(blks,block(kind,i,0,0,blkcode+subseq(code,start,i))))
       else  if not(kind  = "BLOCK"_1 ) then breakblocks(code,i+1,start,blkcode,blks)
        else  let nopara=toint((fsig.rep)_2)
          let args=top(blks,nopara)
          let subblks=cvtlabels(args,1,empty:seq.block)
          if i=length.code then 
             subblks
          else  if  code_(i+1)=exit &and not(kind.subblks_1="LOOPBLOCK"_1 )then
                breakblocks(code,i+2,i+2,empty:seq.sig,push(pop(blks,nopara),
               block("SEQBLKS"_1,blkno.subblks_1,0,0,empty:seq.sig,subblks)))
          else  if i+3 &le length.code &and code_(i+3)=br &and kind.subblks_1="BR"_1 then
                breakblocks(code,i+4,i+4,empty:seq.sig,push(pop(blks,nopara),
               block("BRBLKS"_1,blkno.subblks_1,0,0,subseq(code,i+1,i+3),subblks))        )
          else 
             breakblocks(code,i+1,i+1, blkcode+ascode.subblks ,pop(blks,nopara))
     
 use seq.int
 
 use otherseq.int
 

 
function ascode(subblks1:seq.block) seq.sig
ascode(subblks1,1,[subblks1_1],empty:seq.sig) 
  
    
function =(a:block,b:block) boolean blkno.a=blkno.b
  
function   checkforcase(blk:block) seq.sig
   if  not.iscaseblock.blk  then empty:seq.sig
   else 
       let  t = backparse2(code.blk , length.code.blk-5, 1, empty:seq.int)
       let exp=subseq(code.blk,t_1,length.code.blk-5)
        if @(&or,hasstate,false,exp) then empty:seq.sig
        else exp
  
function  ascode(l:seq.block,i:int,assigned:seq.block,result:seq.sig) seq.sig
    if i > length.assigned then result+block.length.assigned else 
    let   blk=assigned_i
    if kind.blk in "BR " then
         let a2=findblk2(l,1,label2.blk)
          let exp=checkforcase.blk
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
                  ascode(l,i+1,assigned2,result+subseq( code.blk ,1,length.code.blk-5)+keysig.c+eqOp+lit.l1+lit.l2+br)
            else // more than one case block //
              let var=if  islocal.last.exp then last.exp else var.1000
            let prefix=  
            if  islocal.last.exp then subseq((code.blk),1,length.code.blk-6)
          else subseq((code.blk),1,length.code.blk-5) +define."1000"_1
          let z= rearrangecase( caseblks.r, blkno.last.l+1,  defaultlabel.r,var)
           let newl=  if blkno.last.l  < nextblklabel.z-1 then l+block("?"_1,nextblklabel.z-1,0,0,empty:seq.sig) else l
         let first= (allocated.z)_1
         let first1=if isempty.prefix then first else  block(kind.first,blkno.first,label1.first,label2.first,
            prefix+code.first) 
         ascode(newl,i,replace(assigned,i,first1)+subseq(allocated.z,2,length.allocated.z),result)
     else 
     let a1=findblk2(l,1,label1.blk)
     let l1=  findindex(a1,assigned)
     let  assigned1=if  l1 > length.assigned then assigned+a1 else assigned
      let l2=  findindex(a2,assigned1)
      let  assigned2=if  l2 > length.assigned1 then assigned1+a2 else assigned1 
       ascode(l,i+1,assigned2,result+subseq(code.blk,1,length.code.blk-3)+    lit.l1 + lit.l2+br)
    else if kind.blk in "BRC "    then
        let l1=  findindex(label1.blk,1,assigned)
        let assigned1=if l1 > length.assigned then        assigned+findblk2(l,1,label1.blk) else assigned
        let l2=  findindex(label2.blk,1,assigned1)
        let  assigned2=if  l2 > length.assigned1 then  assigned1+findblk2(l,1,label2.blk) else assigned1 
        ascode(l,i+1,assigned2,result+subseq(code.blk,1,length.code.blk-3)+    lit.l1 + lit.l2+br)     
    else   if kind.blk in " LOOPBLOCK  " then
     let a1=findblk2(l,1,label1.blk)
     let l1=  findindex(a1,assigned)
     let  assigned1=if  l1 > length.assigned then assigned+a1 else assigned
     ascode(l,i+1,assigned1,result+code.blk)
    else
      assert kind.blk in "EXIT CONTINUE" report "PROB 4"+kind.blk
       ascode(l,i+1,assigned,result+code.blk)
    
function caseblock(truelabel:int,orgblkno:int,s:sig) caseblock
  let rep =decode.s
  let key= if module.rep="$int" then toint.(fsig.rep)_1
       else 
         assert module.rep="$word" report "unexpected const type"
         hash.(fsig.rep)_1
  caseblock(key,s,truelabel,orgblkno)
  
function caseblock(truelabel:int,orgblkno:int,w:word) caseblock
  caseblock(hash.w,wordsig.w ,truelabel,orgblkno)
  
function findindex(label:int,i:int,a:seq.block) int
   if i > length.a then i else 
  if blkno.a_i=label then i else findindex(label,i+1,a)
 
     
type caseblock is record  key:int,keysig:sig,truelabel:int,orgblkno:int

function print(c:caseblock) seq.word
"&br"+toword.key.c+print.[keysig.c]+toword.truelabel.c+toword.orgblkno.c

use seq.caseblock

function =(a:caseblock,b:caseblock) boolean  key.a=key.b

function ?(a:caseblock,b:caseblock)  ordering key.a ? key.b

function iscaseblock(blk:block) boolean
   let code=code.blk
   let len=length.code
   len > 5 &and kind.blk="BR"_1  &and     isconst.code_(len-4) &and isinOp.code_(len-3) 
   &and not(module.decode.code_(len-4)="$fref")



        
 type gathercaseresult is record caseblks:seq.caseblock, defaultlabel:int
        
function gathercase(l:seq.block, blk:block,exp:seq.sig,   caseblks:seq.caseblock )  gathercaseresult
     // blk is a caseblock but have not created the caseblks yet or check for following case blocks //
       let code=code.blk
   let len=length.code
   let label=blkno.findblk2(l,1,label1.blk)
     let t=  if code_(len-3)=eqOp then
       [caseblock(label,blkno.blk,code_(len-4))]
      else 
       let rep=decode.code_(len-4)
       if module.rep="$words" then
           @(+,caseblock(label,0),empty:seq.caseblock, fsig.rep)
       else 
       assert length.cleancode.rep > 2 &and (cleancode.rep)_1=lit0 report
        "not a standard seq"+print.code
        @(+,caseblock(label,0),empty:seq.caseblock,subseq(cleancode.rep,3,length.cleancode.rep))
// now check to see if following block is a case block //
     let newblock=findblk2(l,1,label2.blk)
     if iscaseblock(newblock) &and subseq(code.newblock,1,length.code.newblock-5)=exp then  gathercase(l,newblock,exp,  caseblks+t )
      else  gathercaseresult(sort(caseblks+t),blkno.newblock) 
      
    
   
     
      
 use otherseq.caseblock   
      
 type     gggresult is record nextblklabel:int,allocated:seq.block  
        
function   rearrangecase( cbs:seq.caseblock, nextblklabel:int,defaultlabel:int,var:sig) gggresult
        if length.cbs=1 then 
           let blklabel=if orgblkno.cbs_1 > 0 then orgblkno.cbs_1 else nextblklabel
                gggresult(if blklabel=nextblklabel then nextblklabel+1 else nextblklabel,
                     [block("BRC"_1,blklabel,truelabel.cbs_1,defaultlabel,[var,keysig.cbs_1,eqOp,lit0,lit0,br])])
        else if length.cbs=2 then
              let blklabel1=if orgblkno.cbs_1 > 0 then orgblkno.cbs_1 else nextblklabel
              let next1=if blklabel1=nextblklabel then nextblklabel+1 else nextblklabel
              let blklabel2=if orgblkno.cbs_2 > 0 then orgblkno.cbs_2 else next1
               let next2=if blklabel2=next1 then next1+1 else next1
                 gggresult(next2,[block("BRC"_1,blklabel1,truelabel.cbs_1,blklabel2,[var,keysig.cbs_1,eqOp,lit0,lit0,br]),
                       block("BRC"_1,blklabel2,truelabel.cbs_2,defaultlabel,[var,keysig.cbs_2,eqOp,lit0,lit0,br])] )
        else 
         let m=(length.cbs / 2)+1
         let middle=cbs_m
              let low= rearrangecase(subseq(cbs,1,m-1),nextblklabel+2,defaultlabel,var) 
              let high=rearrangecase(subseq(cbs,m +1,length.cbs),nextblklabel.low,defaultlabel,var) 
              let lowerlabel=  blkno.(allocated.low )_1
              let upperlabel=  blkno.(allocated.high )_1
               gggresult(nextblklabel.high,  
               [ block("BRC"_1,nextblklabel,upperlabel,nextblklabel+1,[var,keysig.middle,gtOp,lit0,lit0,br]),
               block("BRC"_1,nextblklabel+1,truelabel.middle,lowerlabel,[var,keysig.middle,eqOp,lit0,lit0,br])]
               +allocated.low+allocated.high)
               
       
      
        
    

use otherseq.block            
           
    
function findblk2( l:seq.block,i:int,blkno:int) block
     assert  i &le length.l report "did not find block"   
      let blk=l_i
      if   blkno.blk=blkno then 
        if kind.blk="JMP"_1 then  findblk2(l,1,label1.blk)  else blk
    else findblk2(l,i+1,blkno)  
       
function  ascode( r:set.int,t:block) seq.sig
          if not(blkno.t in r ) then empty:seq.sig
          else  if  kind.t="BR"_1 then
                subseq(code.t,1,length.code.t-3)+
              lit.findindex(label1.t,toseq.r) + lit.findindex(label2.t,toseq.r)+br
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
                 then      let target=if lit0  =(code.b)_1 then label2 else label1
                    block("JMP"_1,blkno.b,target,target,empty:seq.sig) 
         else 
                   block("BR"_1,blkno.b,label1,label2, subseq(code.b,1,length.code.b-1)+[lit0,lit0,br])
             
            
      

use UTF8

use bits

use seq.char

use funcsig

use otherseq.fsignrep

use seq.fsignrep

use otherseq.seq.int

use seq.seq.int

use seq.int

use set.int

use intercode

use libscope

/use mangle


use seq.mytype

use real

use intdict.sig

use ipair.sig

use blockseq.seq.sig

use intdict.seq.sig

use ipair.seq.sig

use seq.seq.seq.sig

use seq.seq.sig

use seq.sig

use set.sig


use intdict.fsignrep

use seq.fsignrep

use stacktrace

use stdlib

use otherseq.word

use seq.seq.word

use seq.word

use set.word

use libdesc


use seq.expmod

use set.seq.word
  

 Function pass2(  abstract:seq.expmod,firstsimple:seq.expmod, placehold:prg,compiled:seq.sig) intercode
   let p= driver(  placehold ,1,emptyprg)  
   let simple=removePH.firstsimple
   let libmods=libdesc(p, simple, abstract)
   let rootsigs=@(+,exports,empty:seq.sig,simple)  
   let t=uses(p,empty:set.sig,asset.rootsigs+libmods)
   let compiled2=asset.removePH.compiled
   let defines2=@(+, defines2(p),empty:seq.sig,toseq.(t-compiled2 )) 
   let sigreps=getfsignrep.p 
    intercode( sigreps ,defines2,t,libmods)
  
  / function dump(f:seq.fsignrep) seq.word
     sort.@(+,printxx,empty:seq.seq.word,f) 
     
  / function printxx(f:fsignrep) seq.word
       fsig.f+ print.cleancode.f 
  
     
  function removePH(s:seq.sig) seq.sig 
    @(+,removePH,empty:seq.sig,s)
    
  function removePH(m:expmod) expmod
 expmod(modname.m,removePH.exports.m,empty:seq.sig,empty:seq.mytype)
 
 function removePH(s:seq.expmod) seq.expmod
     @(+,removePH,empty:seq.expmod,s)
     
function  uses(p:prg,s:sig) seq.sig
 assert not.isplaceholder.s report "A placeholder"+print.s+stacktrace
  // let t=lookupcode(p,s)
  let a=if isempty.t then empty:seq.sig  
  else  code.t_1 //
   let b=cleancode.lookuprep(p,s)
  // assert b=a report "JKL"+print.b+"&br -------------"+print.a //
   b
        
function   uses(p:prg,processed:set.sig, toprocess:set.sig) set.sig
   if isempty.toprocess then  processed else 
    let q= asset.@(+,uses.p,empty:seq.sig,     toseq.toprocess)
      uses(p,processed &cup toprocess, q-processed)


function defines2(p:prg,ss:sig) seq.sig
if isconst.ss &or islocal.ss then empty:seq.sig else 
let s=lookuprep(p,ss)
if (module.s)_1 in "$ "  &or length.cleancode.s=0 
 &or  isabstract.mytype.module.s  
 then empty:seq.sig
 else   [ss]

function check(p:prg,ss:sig) seq.sig
let  s=lookuprep(p,ss)
if (length.module.s=1 &and (module.s)_1 in "$  local $fref $constant $words $word $int" ) 
&or isabstract.mytype.module.s then empty:seq.sig
else if  "T"_1 in fsig.s then [ss] else empty:seq.sig

type backresult is record code:seq.sig, places:seq.int


 
Function firstopt(p:prg, rep:fsignrep, code:seq.sig) prg
 let nopara = noparafsignrep.rep
 let pdict=addpara(empty:intdict.seq.sig, nopara)
 let code2 = value.yyy(p, code, 1, nopara + 1, pdict)
 let rep2=removePH.rep
 let s=sig55( fsig.rep2,module.rep2,code2,returntype.rep2)
 let a = breakblocks(code2,s)
 let a2=value.yyy(p,a,1,nopara+1,pdict)
  add(p, s, a2) 
  
/Function firstopt(p:prg, sin:sig, code:seq.sig) prg
 let nopara = nopara.sin
 let pdict=addpara(empty:intdict.seq.sig, nopara)
 let code2 = value.yyy(p, code, 1, nopara + 1, pdict)
 let s=  removePH.sin
 let a = breakblocks(code2,s)
 let a2=value.yyy(p,a,1,nopara+1,pdict)
  add(p, s, a2) 
   
   use process.int
    
function print(s:seq.int)seq.word @(+, toword,"", s)


function var(i:int)sig var.toword.i

function var(w:word)sig  sig([ w],  "local","?")


function addpara(map:intdict.seq.sig, i:int)intdict.seq.sig
 if i ≤ 0 then map
 else
  let v = var.i
   addpara(add(map, valueofencoding.v, [ v]), i - 1)

function addlooplocals(map:intdict.seq.sig, firstvar:int, nextvar:int, nopara:int, i:int)intdict.seq.sig
 if i = nopara then map
 else
  addlooplocals(replace(map, valueofencoding.var(firstvar + i), [ var(nextvar + i)]), firstvar, nextvar, nopara, i + 1)
  
function yyy(p:prg, s:seq.sig, i:int, nextvar:int, map:intdict.seq.sig)ipair.seq.sig
 // assert length.s < 12 &or"CONTINUE"_1 in print.s &or not("367"_1 in print.s &or"365"_1 in print.s)report"BB"+ toword.length.s + toword.i + print.subseq(s, 1, i)+">>>>"+ print.subseq(s, i + 1, length.s)//
 if i > length.s then ipair(nextvar, s)
 else if islocal.s_i then
 let t = lookup(map, valueofencoding.s_i)
   if isempty.t then yyy(p, s, i + 1, nextvar, map)
   else yyy(p, replace(s, i, 1, t_1), i + length.t_1, nextvar, map)
  else if isinline.s_i then
 let t = inline(p, s, i, nextvar)
   yyy(p, code.t, index.t, nextvar.t, map)
else   if s_i=br &and s_(i-3)=notOp then
  yyy(p,replace(s,i-3,3,[s_(i-1),s_(i-2)]),i,nextvar,map)
else if isplaceholder.s_i then
            yyy(p,replace(s,i,1,[removePH.s_i]),i,nextvar,map)
else    if not.lookcloser.s_i then yyy(p, s, i + 1, nextvar, map) else
     let rep=decode.s_i
  if isdefine.s_i then
   if i > 1 ∧ (isconst.s_(i - 1) ∨ islocal.s_(i - 1))then
   yyy(p, replace(s, i - 1, 2, empty:seq.sig), i - 1, nextvar, replace(map, valueofencoding.(cleancode.rep)_1, [ s_(i - 1)]))
   else
    yyy(p, replace(s, i, 1, [ define.toword.nextvar]), i + 1, nextvar + 1, replace(map, valueofencoding.(cleancode.rep)_1, [ var.nextvar]))
 else 
   if module.rep="$" then optmodule$(p, s, i , nextvar, map,rep)
 else 
   let nopara= nopara.s_i 
    if nopara=0 &or nopara > 2 &or not(isconst.s_(i - 1)) then yyy(p, s, i + 1, nextvar, map)
 else 
  // one or two parameters with last arg being constant //
 if nopara = 1 then optoneop(p, s, i , nextvar, map,rep)
 else // should add case of IDXUC with record as first arg //
  // assert not((fsig.rep)_1="encode"_1) report "HERE"+fsig.rep //
  if fsig.rep in[ "decode(T erecord, T encoding)","decode(char seq erecord, char seq encoding)"] ∧ s_(i - 2) = wordEncodingOp  
 &and module.rep="char seq encoding" then
  let arg1 = decode.s_(i - 1)
   if module.arg1 = "$word"then
   let a1 = @(+, lit, empty:seq.sig, tointseq.decodeword.(fsig.arg1)_1)
    let d = [ lit.0, lit.length.a1] + a1 + RECORD(length.a1 + 2)
  //  let k = replace(s, i - 2, 3, d) //
     yyy(p, replace(s, i - 2, 3, d), i + length.d - 3, nextvar, map)
   else yyy(p, s, i + 1, nextvar, map)
  else if fsig.rep  in[ "encode(T erecord,T)","encode(char seq erecord, char seq)"] ∧ s_(i - 2) = wordEncodingOp  
    &and module.rep="char seq encoding" then
  let arg1 = decode.s_(i - 1)
   if module.arg1 = "$constant"then
      let chseq=  @(+,  value,empty:seq.int,subseq(cleancode.arg1,3,length.cleancode.arg1))
      // assert false report "in encode opt"+@(+,toword,"",chseq)  +module.rep //
        assert  @(&and, islit,true,  subseq(cleancode.arg1,3,length.cleancode.arg1)) report "const problem" 
       let new=   wordsig.encodeword.@(+,char,empty:seq.char,chseq)
      yyy(p, replace(s, i - 2, 3, [new]), i - 2, nextvar, map)
   else yyy(p, s, i + 1, nextvar, map)
 else if not.isconst.s_(i - 2) then  yyy(p, s, i + 1, nextvar, map)
 else  
  //  two parameters with   constant  args //
   if module.rep="builtin" then opttwoopbuiltin(p, s, i , nextvar, map,rep)
   else  
       //   assert not(last.module.rep="seq"_1) &or (fsig.rep)_1="+"_1 report "HERE"  +fsig.rep //
    if  (fsig.rep)_1="_"_1 &and last.module.rep="seq"_1 then
     // only checks name="_" in module seq with to arguments and assumes is index function. 
      A better check is done when lookcloserbit is set on sig in upperbits //
  let idx = value.s_(i - 1)
  let arg1 = decode.s_(i - 2)
  let words = name.arg1
   if module.arg1 = "$words" &and  between(idx, 1, length.words) then
      yyy(p, replace(s, i - 2, 3, [ wordsig.words_idx]), i - 1, nextvar, map)
   else if    module.arg1 = "$constant" &and  between(idx, 1, length.cleancode.arg1-2) then
      yyy(p, replace(s, i - 2, 3, [ (cleancode.arg1)_(idx+2)]), i - 1, nextvar, map)
   else yyy(p, s, i + 1, nextvar, map)
 else   if  fsig.rep in ["+(T seq, T seq)","+(word seq, word seq)"] &and module.rep="word seq" then
 let arg1 = decode.s_(i - 2)
  let arg2 = decode.s_(i - 1)
   if module.arg1 = "$words" ∧ module.arg2 = "$words"then
     yyy(p, replace(s, i - 2, 3, [ wordssig(name.arg1 + name.arg2)]), i - 1, nextvar, map)
   else yyy(p, s, i + 1, nextvar, map)
 else yyy(p, s, i + 1, nextvar, map)
 
function optoneop(p:prg, s:seq.sig, i:int, nextvar:int, map:intdict.seq.sig,rep:fsignrep)ipair.seq.sig
 if fsig.rep = "makereal(word seq)" then
 let arg1 = decode.s_(i - 1)
   if module.arg1 = "$words"then
   let  x=lit.representation.makereal.fsig.arg1 
     yyy(p, replace(s, i - 1, 2, [ x]), i, nextvar, map)
   else yyy(p, s, i + 1, nextvar, map)
 else if fsig.rep = "merge(word seq)" then
 let arg1 = decode.s_(i - 1)
   if module.arg1 = "$words"then
     yyy(p, replace(s, i - 1, 2, [ wordsig.merge.fsig.arg1 ]), i, nextvar, map)
   else yyy(p, s, i + 1, nextvar, map)
else yyy(p, s, i + 1, nextvar, map)

function opttwoopbuiltin(p:prg, s:seq.sig, i:int, nextvar:int, map:intdict.seq.sig,rep:fsignrep)ipair.seq.sig
 if s_i = IDXUC   then
    let j = value.s_(i - 1)
    let x = decode.s_(i - 2)
    if between(j, 0, length.cleancode.x - 1)then
      yyy(p, replace(s, i - 2, 3, [(cleancode.x)_(j + 1)]), i - 1, nextvar, map)
    else yyy(p, s, i + 1, nextvar, map)
 else  if s_i = plusOp then 
   let new= replace(s, i - 2, 3, [ lit(value.s_(i - 2) + value.s_(i - 1))])
   yyy(p,new,i-1,nextvar,map)
 else if fsig.rep="*(int,int)" then
   let new=replace(s, i - 2, 3, [ lit(value.s_(i - 2) * value.s_(i - 1))])
    yyy(p,new,i-1,nextvar,map)
 else if fsig.rep="-(int,int)" then
   let new= replace(s, i - 2, 3, [ lit(value.s_(i - 2) - value.s_(i - 1))])
   yyy(p,new,i-1,nextvar,map)
 else if fsig.rep="/(int,int)" ∧ value.s_(i - 1) ≠ 0 then
  let new=replace(s, i - 2, 3, [ lit(value.s_(i - 2) / value.s_(i - 1))])
   yyy(p, new, i - 1 , nextvar , map)
 else if fsig.rep="=(int,int)"  then
   let new=replace(s, i - 2, 3, [ if  s_(i - 2) =  s_(i - 1)  then lit.1 else lit.0])
  yyy(p,new,i-1,nextvar,map)
 else if fsig.rep=">(int,int)"  then
   let new=replace(s, i - 2, 3, [ if value.s_(i - 2) > value.s_(i - 1)  then lit.1 else lit.0])
  yyy(p,new,i-1,nextvar,map)
   else if fsig.rep="∨ (bits, bits)" then
  let new=replace(s, i - 2, 3, [ lit.toint(bits.value.s_(i - 2) &or bits.value.s_(i - 1))])
  yyy(p,new,i-1,nextvar,map)
  else if fsig.rep="∧ (bits, bits)" then
  let new=replace(s, i - 2, 3, [ lit.toint(bits.value.s_(i - 2) &and bits.value.s_(i - 1))])
  yyy(p,new,i-1,nextvar,map)
 else if fsig.rep="<<(bits, int)" then
  let new=replace(s, i - 2, 3, [ lit.toint(bits.value.s_(i - 2) << value.s_(i - 1))])
  yyy(p,new,i-1,nextvar,map)
 else if  fsig.rep=">>(bits, int)"then
  let new=replace(s, i - 2, 3, [ lit.toint(bits.value.s_(i - 2) >> value.s_(i - 1))])
  yyy(p,new,i-1,nextvar,map)
 else if fsig.rep="-(real,real)" then 
  let new= replace(s, i - 2, 3, [ lit.representation(casttoreal.value.s_(i - 2) - casttoreal.value.s_(i - 1))])
  yyy(p,new,i-1,nextvar,map)
  else yyy(p, s, i + 1, nextvar, map)
  
function optmodule$(p:prg, s:seq.sig, i:int, nextvar:int, map:intdict.seq.sig,rep:fsignrep)ipair.seq.sig
if  fsig.rep="BLOCK 3" then
    let t = backparse(s, i - 1, 3, empty:seq.int) + i
     let condidx=t_2-4
     let cond=s_ condidx
     if   s_( condidx+3)=br  &and isconst(cond) then
        let keepblock=if value.cond=1 then value.s_(condidx+1) else value.s_(condidx+2)
             let new=subseq(s,t_keepblock,t_(keepblock+1)-2)
     // "BB"+print.subseq(s,t_1,i)
      +"PP"+    print.subseq(s,t_keepblock,t_(keepblock+1)-2)//
        yyy(p, replace(s, condidx, i-condidx+1, new), condidx+length.new, nextvar, map) 
    else 
     yyy(p, s, i + 1, nextvar, map)
else if  (fsig.rep)_1="LOOPBLOCK"_1 then
    let nopara = nopara.s_i - 1
    let firstvar = value.s_(i - 1)
   yyy(p, replace(s, i - 1, 1, [ lit.nextvar]), i + 1, nextvar + nopara, addlooplocals(map, firstvar, nextvar, nopara, 0))
else if (fsig.rep)_1="RECORD"_1 then
 let nopara = nopara.s_i
  let args = subseq(s, i - nopara, i - 1)
   if @(∧, isconst, true, args) ∧ length.args = nopara then
     yyy(p, replace(s, i - nopara, nopara + 1, [ constant.args]), i - nopara, nextvar, map)
   else yyy(p, s, i + 1, nextvar, map)
else if  (fsig.rep)_1="APPLY"_1 then
   let t = applycode(p, nextvar, s, i)
   yyy(p, code.t, index.t, nextvar.t, map)
else yyy(p, s, i + 1, nextvar, map)

 
 
function islit(s:sig) boolean   module.decode.s ="$int" 


 function inline(p:prg, s:seq.sig, i:int, nextvar:int)expandresult
 let k = lookuprep(p, s_i)
 if fsig.k="parabits(int)" then  expandresult(nextvar,i+1,s) else
  let code =   if (last.cleancode.k=optionOp) then subseq(cleancode.k,1,length.cleancode.k-2) else   cleancode.k
 // assert not((print.[ s_i])_1 = "message"_1)report print.[ s_i] + if issimple.k then"SIMPLE"else"" //
  let nopara = noparafsignrep.k
   if length.code = 1 ∧ code = [ var.1]then
   // function just returns result // expandresult(nextvar, i, replace(s, i, 1, empty:seq.sig))
   else
    let t = backparse(s, i - 1, nopara, empty:seq.int) + i
     assert length.t = nopara + 1 report"INLINE PARA" + print.subseq(s, 1, i)
     let new = if issimple.k then expandsimpleinline(s, t, empty:intdict.seq.sig, nopara, nextvar, code, p)
     else 
       let z= expandinline(s, t, empty:intdict.seq.sig, nopara, empty:seq.sig, nextvar, code, p)
    //     assert false report "not simple inline"+print.z
         +"&br -------------------"+print.subseq( s, t_1, i) //
        z
      expandresult(nextvar + nopara, t_1 + length.new, replace(s, t_1, i - t_1 + 1, new))



function expandsimpleinline(s:seq.sig, t:seq.int, pmap:intdict.seq.sig, i:int, nextvar:int, inlinecode:seq.sig, p:prg)seq.sig
 // when i > 0 then building paramenter map //
 if i = 0 then value.yyy(p, inlinecode, 1, nextvar, pmap)
 else
  expandsimpleinline(s, t, add(pmap, valueofencoding.var.i, subseq(s, t_i, t_(i + 1) - 1)), i - 1, nextvar, inlinecode, p)

function expandinline(s:seq.sig, t:seq.int, pmap:intdict.seq.sig, i:int, newcode:seq.sig, nextvar:int, inlinecode:seq.sig, p:prg)seq.sig
 // when i > 0 then assigning parameters to new local variables //
 if i = 0 then newcode+value.yyy(p, inlinecode, 1, nextvar, pmap)
 else
  expandinline(s, t, add(pmap, valueofencoding.var.i, [ var.nextvar]), i - 1, 
  subseq(s, t_i, t_(i + 1) - 1) + define.toword.nextvar +newcode, nextvar + 1, inlinecode, p)

function backparse(s:seq.sig, i:int, no:int, result:seq.int)seq.int
 if no = 0 then result
 else
  assert i > 0 report"back parse 1" + toword.no+print.s
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
     
function backparse2(s:seq.sig, i:int, no:int, result:seq.int)seq.int
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

function replace(s:seq.sig, start:int, length:int, value:seq.sig)seq.sig
 subseq(s, 1, start - 1) + value + subseq(s, start + length, length.s)

function adddefines2(s:seq.sig, t:seq.int, i:int, nopara:int, newcode:seq.sig, nextvar:int)seq.sig
 if i > nopara then newcode
 else
  adddefines2(s, t, i + 1, nopara, newcode + subseq(s, t_i, t_(i + 1) - 1)
  + define.toword(nextvar + i - 1), nextvar)

type expandresult is record nextvar:int, index:int, code:seq.sig

function applycode(p:prg, nextvar:int, code:seq.sig, index:int)expandresult
 let pseq = code_(index - 1)
 let term1 = cleancode.decode.code_(index - 2)
 let term2 = cleancode.decode.code_(index - 3)
 let nopara1 = nopara.term1_1 - 2
 let nopara2 = nopara.term2_1 - 1
 let allpara = @(+, var, empty:seq.sig, arithseq(nopara1 + nopara2 + 2, 1, nextvar))
 let map1 = add(empty:intdict.seq.sig, valueofencoding.var."term1para"_1, subseq(allpara, 1, nopara1))
 let map2 = add(map1, valueofencoding.var."term2para"_1, subseq(allpara, nopara1 + 1, nopara1 + nopara2))
 let map3 = add(map2, valueofencoding.var."term1"_1, term1)
 let map4 = add(map3, valueofencoding.var."term2"_1, term2)
 let map5 = add(map4, valueofencoding.var."FREFpseq"_1, [ pseq])
 let t = backparse(code, index - 4, nopara1 + nopara2 + 2, empty:seq.int)
 let noop = nopara1 + nopara2 = 0 ∧ checknoop.term2 ∧ t_2 - t_1 = 1
 ∧ code_(t_1) = emptyseqOp ∧ checkcat(decode.term1_1 )
 ∧ not((fsig.decode.term2_1)_1 = "deepcopy"_1)
  if noop then
   let new = subseq(code, 1, t_1 - 1) + subseq(code, t_2, index - 4)
  // assert not(subseq(code, t_2, index - 4)=[var.1]) report "XXXX"+print.code+"/new/"+print.new //
    expandresult(nextvar, length.new + 1, new + subseq(code, index + 1, length.code))
  else
   let paras = adddefines2(code, t + (index - 3), 1, nopara1 + nopara2 + 2, empty:seq.sig, nextvar)
   let body = yyy(p, applytemplate, 1, nextvar + nopara1 + nopara2 + 2, map5)
   let new = paras + subseq(allpara, nopara1 + nopara2 + 1, length.allpara) + value.body
    // assert false report"APPLY"+ print.new +"
&p"+ print.code +"
&p"+ print.t +"<"+ toword(nopara1 + nopara2 + 2)//
    expandresult(index.body, t_1 + length.new, replace(code, t_1, index - t_1 + 1, new))

function checknoop(s:seq.sig)boolean
 if length.s ≠ 1 then false
 else if s_1 = var.1 then true
 else
  // assert false report let t = code.decode.s_1 print.t + if t_1 = var.1 &and length.t = 1 then"T"else"F"//
  checknoop.cleancode.decode.s_1
  
function checkcat(f:fsignrep) boolean
 let p=subseq(module.f,1,length.module.f-1)
  last.module.f = "seq"_1
 ∧   fsig.f = "+("+p+  "seq,"+p+")"

function applytemplate seq.sig
let theseq = 5
let stk = 6
 [ lit.0, lit.4, loopblock.4, var.theseq, lit.0, IDXUC, var."FREFpseq"_1, eqOp, lit.3, lit.4
 , br, var.4, var.theseq, lit.2, IDXUC, var.stk, var.theseq, lit.3, IDXUC, STKRECORD
 , continue.3, var.theseq, lit.1, IDXUC, define."8"_1, var.4, lit.1, lit.9, loopblock.3, var.10
 , var.8, gtOp, lit.3, lit.4, br, var.9, exit, var."term2para"_1, var.theseq, lit.0
 , IDXUC, lit.0, eqOp, lit.2, lit.3, br, var.theseq, var.10, lit.1, plusOp
 , IDXUC, exit, var.theseq, lit.0, IDXUC, var.theseq, var.10, CALLIDX, exit, block.3
 , var."term2"_1, define."11"_1, var."term1para"_1, var.9, var.11, var."term1"_1, var.10, lit.1, plusOp, continue.2
 , block.4, define."7"_1, var.stk, lit.0, eqOp, lit.5, lit.6, br, var.7, exit
 , var.7, var.stk, lit.1, IDXUC, var.stk, lit.0, IDXUC, continue.3, block.6]

use seq.target
  
function driver(knownsymbols:prg,i:int,processed:prg) prg
if i > length.keys.knownsymbols then processed
else 
    driver(knownsymbols,i+1,depthfirst(knownsymbols,processed,ecvt.(keys.knownsymbols)_i))
    

function depthfirst(knownsymbols:prg,processed:prg,s:sig) prg
      // let f=lookuprep(knownsymbols,s) //
      let code=lookupcode(knownsymbols,s)
      if isempty.code then knownsymbols else
      depthfirst(knownsymbols,1,[s],processed,code.code_1,s)


function     depthfirst(knownsymbols:prg,i:int,pending:seq.sig,processed:prg,code:seq.sig,s:sig) prg
        if i > length.code then
                 firstopt(processed,decode.s,code)
        else 
         let this=code_i
  let newprg=if not.isplaceholder.this then   processed 
    else 
      let rep=  lookuprep(knownsymbols, this)
     let q= if module.rep="$fref" then     (constantcode.rep)_1 else this
      if    q in pending then 
         processed  
    else
         let  rep2=if module.rep="$fref" then lookuprep(knownsymbols, q) else rep
          let r= findencode(removePH.rep2)
          if isempty.r &and  length.cleancode.rep2 > 0 then 
          depthfirst(knownsymbols, 1,pending+q,processed,cleancode.rep2,q)
          else processed
        depthfirst(knownsymbols,   i +  1, pending, newprg,code,s)




