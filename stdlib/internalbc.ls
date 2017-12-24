
Module internalbc

*  64+2*3  instead of 64+ 2 * 3 does not give reasonable error message!

use stdlib

use llvm

use bitstream


Function BLOCKCOUNT(slot:int, a1:int) internalbc
  addstartbits(1,1, add(a1,emptyinternalbc))
  
Function RET(slot:int, a1:int) internalbc
  addstartbits(INSTRET,1, addaddress(slot,a1,emptyinternalbc))

Function RET(slot:int) internalbc
  addstartbits(INSTRET,0,emptyinternalbc)
  
Function CAST(slot:int, a1:int, a2:int, a3:int) internalbc
       addstartbits(INSTCAST,3,addaddress(slot,a1,add(a2,add(a3,emptyinternalbc))))

Function BR(slot:int, a1:int, a2:int, a3:int) internalbc
       addstartbits(INSTBR,3,add(a1,add(a2,addaddress(slot,a3,emptyinternalbc))))
       
Function BR(slot:int, a1:int) internalbc
       addstartbits(INSTBR,1,add(a1,emptyinternalbc))


Function GEP(slot:int, a1:int, a2:int, a3:int,a4:int) internalbc
       addstartbits(INSTGEP,4,add(a1,add(a2,addaddress(slot,a3,addaddress(slot,a4,emptyinternalbc)))))
       
Function GEP(slot:int, a1:int, a2:int, a3:int,a4:int,a5:int) internalbc
       addstartbits(INSTGEP,5,add(a1,add(a2,addaddress(slot,a3,addaddress(slot,a4,addaddress(slot,a5,emptyinternalbc))))))
       
Function STORE(slot:int, a1:int, a2:int, a3:int,a4:int) internalbc
       addstartbits(INSTSTORE,4,addaddress(slot,a1,addaddress(slot,a2,add(a3,add(a4,emptyinternalbc)))))

       
Function BINOP(slot:int, a1:int, a2:int, a3:int,a4:int) internalbc
       addstartbits(INSTBINOP,4,addaddress(slot,a1,addaddress(slot,a2,add(a3,add(a4,emptyinternalbc)))))

Function BINOP(slot:int, a1:int, a2:int, a3:int) internalbc
       addstartbits(INSTBINOP,3,addaddress(slot,a1,addaddress(slot,a2,add(a3,emptyinternalbc))))


Function LOAD(slot:int, a1:int, a2:int, a3:int,a4:int) internalbc
       addstartbits(INSTLOAD,4,addaddress(slot,a1,add(a2,add(a3,add(a4,emptyinternalbc)))))


Function CALL(slot:int, a1:int, a2:int, a3:int,a4:int) internalbc
        addstartbits( INSTCALL,4,add(a1, add( a2,add(a3,addaddress ( slot,a4,emptyinternalbc)))))

Function CALL(slot:int, a1:int, a2:int, a3:int,a4:int,a5:int) internalbc
        addstartbits(INSTCALL,5,add(a1, add( a2,add(a3,addaddress ( slot,a4,addaddress(slot,a5,emptyinternalbc))))))


Function CALL(slot:int, a1:int, a2:int, a3:int,a4:int,a5:int,a6:int) internalbc
        addstartbits(INSTCALL,6,add(a1, add( a2,add(a3,addaddress ( slot,a4,addaddress(slot,a5,addaddress(slot,a6,emptyinternalbc)))))))

Function CALL(slot:int, a1:int, a2:int, a3:int,a4:int,a5:int,a6:int,a7:int) internalbc
        addstartbits(INSTCALL,7,add(a1, add( a2,add(a3,addaddress ( slot,a4,addaddress(slot,a5,addaddress(slot,a6,addaddress(slot,a7,emptyinternalbc))))))))

Function CALL(slot:int, a1:int, a2:int, a3:int,a4:int,a5:int,a6:int,a7:int,a8:int) internalbc
        addstartbits( INSTCALL,8,add(a1, add( a2,add(a3,addaddress ( slot,a4,addaddress(slot,a5,addaddress(slot,a6,addaddress(slot,a7,addaddress(slot,a8,emptyinternalbc)))))))))

Function CALL(slot:int, a1:int, a2:int, a3:int,a4:int,a5:int,a6:int,a7:int,a8:int,a9:int) internalbc
        addstartbits( INSTCALL,9,add(a1, add( a2,add(a3,addaddress ( slot,a4,addaddress(slot,a5,addaddress(slot,a6,
        addaddress(slot,a7,addaddress(slot,a8,addaddress(slot,a9,emptyinternalbc))))))))))


Function CALL(slot:int, a1:int, a2:int, a3:int,a4:int,a5:int,rest:seq.int) internalbc
        addstartbits( INSTCALL,5+length.rest,add(a1, add( a2,add(a3,addaddress ( slot,a4,addaddress(slot,a5,args(slot,emptyinternalbc,rest,length.rest)))))))


function args(slot:int,t:internalbc,rest:seq.int,i:int) internalbc
     if i = 0 then t else   args(  slot,addaddress(slot,rest_i,t) ,rest,i-1)


Function CMP2(slot:int, a1:int, a2:int, a3:int) internalbc
       addstartbits(INSTCMP2,3,addaddress(slot,a1,addaddress(slot,a2,add(a3,emptyinternalbc))))
       
Function PHI(slot:int, a1:int, a2:int, a3:int,a4:int,a5:int,a6:int,a7:int) internalbc
        addstartbits(INSTPHI,7,add(a1,addsignedaddress(slot,a2,add(a3,addsignedaddress(slot,a4,add(a5,
        addsignedaddress(slot,a6,add(a7,emptyinternalbc))))))))
        
Function PHI(slot:int, a1:int, a2:int, a3:int,a4:int,a5:int) internalbc
        addstartbits(INSTPHI,5,add(a1,addsignedaddress(slot,a2,add(a3,addsignedaddress(slot,a4,add(a5,emptyinternalbc))))))

Function PHI(slot:int,a1:int,s:seq.int) internalbc
       addstartbits(INSTPHI,length.s+1,add(a1,subphi(slot,emptyinternalbc,s,length.s)))

function     subphi(slot:int,b:internalbc,s:seq.int,i:int) internalbc
       if i > 1 then 
          subphi(slot,addsignedaddress(slot,s_(i-1),add(s_i,b)),s,i-2)
       else b

Function phiinst(slot:int,tailphi:seq.int,nopara:int,p:int)  internalbc 
  let t=@(addpair(tailphi,slot+p,p),identity,emptyinternalbc,arithseq(length.tailphi / (nopara + 1),-nopara-1,length.tailphi -nopara ) )
     addstartbits(INSTPHI,length.tailphi / (nopara + 1) * 2 + 3,  add(typ.i64,addsignedaddress(slot+p,-p-1,add(0,t))))

Function   phiinst(tailphi:seq.int,nopara:int)  internalbc  
   let slot=nopara+1
@(+,phiinst(slot,tailphi,nopara),emptyinternalbc,arithseq(nopara,1,1))

Function  addpair(    tailphi:seq.int,  slot:int,p:int,a:internalbc,b:int) internalbc
          addsignedaddress(slot,tailphi_(b+p),add(tailphi_b,a))
 
  (block1,p11,p12,p13,block2,p21,p22,p23)   phi(p11,block1,p21,block2)


  function phiinst(slot:int,typ:int,tailphi:seq.int,nopara:int,p:int)  internalbc 
  let t=@(addpair(tailphi,slot+p,p),identity,emptyinternalbc,arithseq(length.tailphi / (nopara + 1),-nopara-1,length.tailphi -nopara ) )
     addstartbits(INSTPHI,length.tailphi / (nopara + 1) * 2 + 1,    add(typ,t))
     
   

Function   phiinst(slot:int,typ:int,tailphi:seq.int,nopara:int)  internalbc  
@(+,phiinst(slot,typ,tailphi,nopara),emptyinternalbc,arithseq(nopara,1,1))



  Function addstartbits(inst:int,noargs:int,c:internalbc)  internalbc 
     if noargs > 31 &or inst > 31 * 31 then
           internalbc(3 ,4,[    vbr6,inst, vbr6,noargs]+ finish.c)
     else 
     if inst  < 32 then 
     let b = if  bitcount.c > 40 then internalbc(0,0,finish.c) else c
     internalbc( ((bits.b * 64 + noargs) * 64 + inst) * 16 + 3  ,bitcount.b+(6+6+4),done.b)
     else 
     let b = if  bitcount.c > 34 then internalbc(0,0,finish.c) else c
     internalbc( (((bits.b * 64 + noargs) * 64 + inst / 32 ) * 64 + inst mod 32 +32) * 16 + 3  ,bitcount.b+(6+6+6+4),done.b)
       
    
type internalbc is record  bits:int,bitcount:int, done:seq.int 

Function emptyinternalbc internalbc  internalbc(0,0,empty:seq.int)

Function +(a:internalbc,b:internalbc ) internalbc
  if   length.done.a > 0 &or bitcount.a+bitcount.b > 56 then internalbc(bits.a,bitcount.a,done.a+finish.b)
  else   internalbc( bits.b * 2 ^ bitcount.a + bits.a,bitcount.a+bitcount.b,done.b)

function finish(b:internalbc) seq.int
 if bitcount.b = 0 then done.b else 
  [bits.b * 64 + bitcount.b]+done.b
  
function addaddress(slot:int,a:int,b:internalbc) internalbc
   if -a > slot then
      internalbc(0,0,[-a,slot]+finish.b)
   else 
   if a < 0 then  add(slot+a,b)
   else   internalbc(0,0,[reloc,a-slot+1]+finish.b)
   
function addsignedaddress(slot:int,a:int,b:internalbc) internalbc
   if a &le 0 then  
       let v = slot+a
       let c=if v &ge 0 then  2 * v   else (2 * -v + 1)
   add(c,b)
   else   
    internalbc(0,0,[relocsigned,a-slot+1]+finish.b)


function add(val:int,b:internalbc) internalbc
     if val > 31 then   internalbc(0,0,[vbr6,val]+finish.b)
     else 
     let newbitcount=6+bitcount.b
     if newbitcount > 56 then   internalbc(val,6,finish.b)        
     else internalbc(  bits.b *  64 + val ,newbitcount,done.b)
     
     
Function tobitstream(offset:int,b:internalbc) bitstream
  processit(offset, finish.b, 1, emptyx, 0, 0)
  

  
function processit(offset:int,s:seq.int,i:int,result:bitstream,val1:int,val2:int)  bitstream
 if  i > length.s then  result
 else let val=s_i let nobits= val mod 64 let bits = val / 64
   if nobits < 58 then processit(offset,s,i+1,addbits(result,bits, nobits ),val1,val2)
   else 
   if val=reloc then 
       processit(offset,s,i+2,addvbr6(result,offset-s_(i+1)),val1,val2)
    else  if val=vbr6 then
          processit(offset,s,i+2,addvbr6(result,s_(i+1)),val1,val2)
    else if val = sub11 then
      processit( offset,s,i+2,addvbr6(result,offset-(val1-s_(i+1)+1)),val1,val2)
    else if val = sub22 then
         processit(offset,s,i+2,addvbr6(result,offset-(val2-s_(i+1)+1)),val1,val2)
    else if val = relocsigned then
          processit(offset,s,i+2,addvbrsigned6(result,offset-s_(i+1)),val1,val2) 
    else  
      assert val=setsub report "invalid code"
          let slot=s_(i+1)
          let v1 = s_(i+2)
          let v2 = s_(i+3)
        processit(offset+slot,s,i+4,result,if v1  &le   0 then  offset-v1 else v1,if v2 &le 0 then  offset-v2 else v2)
      
      
Function usetemplate(deltaoffset:int,t:internalbc,val1:int,val2:int) internalbc
      internalbc(0,0,[setsub,deltaoffset,if val1 < 0 then val1 + 1 else val1 ,if val2 < 0 then val2 + 1 else val2 ] +finish.t +[setsub,-deltaoffset,0,0])
           
      
function reloc int 63  

function vbr6  int 63+64


Function ibcsub1  int -60

Function ibcsub2  int -61

function sub11 int 60

function sub22 int 61

function setsub int 63 + 64 * 2

function relocsigned int 63 + 64 * 3


Function INSTCALL int 34

Function INSTRET int 10

Function INSTCAST int // CAST:[ opcode, ty, opty, opval]// 3

Function INSTSELECT int 5

Function INSTBR int 11

Function INSTPHI int 16

Function INSTCMP2 int 28

Function INSTBINOP int 2

Function INSTBLOCK int 1

Function INSTNOPARA int -1

Function INSTALLOCA int 19

Function INSTLOAD int 20

Function INSTSTORE int 44

Function INSTGEP int 43



