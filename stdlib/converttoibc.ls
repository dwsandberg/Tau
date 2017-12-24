
module cvttointernalbc 

use llvm

use internalbc

use stdlib

use seq.seq.int

Function cvttoibc(
 s:seq.seq.int,i:int,slot:int,result:internalbc) internalbc
  if i > length.s then result
  else
   let d = s_i
  let tp=d_1
  let len = length.d
  if tp = -1 then cvttoibc(s,i+1,slot+d_2,result)
   else 
     let bits=
       if len=2 then
          if tp=INSTRET then RET(slot,d_2)
          else  if tp=INSTBR  then BR(slot,d_2)
          else  assert tp=1 report "NOT HANDLED as ibc"+ @(+,toword,"",d)
            BLOCKCOUNT(slot,d_2)
       else if len = 4 then
            if tp=INSTCMP2 then  CMP2(slot,d_2,d_3,d_4)
            else if tp = INSTBR then BR(slot,d_2,d_3,d_4)
             else          if tp=INSTBINOP then
          BINOP(slot,d_2,d_3,d_4)
            else
            assert tp=INSTCAST report "NOT HANDLED"+ @(+,toword,"",d)
            CAST(slot,d_2,d_3,d_4)
       else if len = 5 then
         if tp=INSTLOAD then
           LOAD(slot,d_2,d_3,d_4,d_5)
         else          if tp=INSTBINOP then
          BINOP(slot,d_2,d_3,d_4,d_5)
         else if tp=INSTSTORE then
          STORE(slot,d_2,d_3,d_4,d_5)
         else if tp=INSTCALL then
          CALL(slot,d_2,d_3,d_4,d_5)
         else
        assert tp=INSTGEP report "NOT HANDLED"+ @(+,toword,"",d)
        GEP(slot,d_2,d_3,d_4,d_5)
       else if len=6 then
         if tp=INSTPHI then
          PHI(slot,d_2,d_3,d_4,d_5,d_6)
        else         if tp=INSTCALL then
          CALL(slot,d_2,d_3,d_4,d_5,d_6)
        else
          assert tp=INSTGEP  report "NOT HANDLED"+ @(+,toword,"",d)
           GEP(slot,d_2,d_3,d_4,d_5,d_6)
       else if tp=INSTCALL then
         CALL(slot,d_2,d_3,d_4,d_5,d_6,subseq(d,7,len))
        else if tp=INSTPHI  then
          PHI(slot,d_2,subseq(d,3,len))
        else 
        if tp=INSTRET &and len=1 then
          RET(slot)
        else
           assert false report "NOT HANDLED"+ @(+,toword,"",d)
           emptyinternalbc
   let slotinc=    { if tp in [ INSTLOAD, INSTALLOCA, INSTCALL, INSTGEP, INSTCAST, INSTCMP2, INSTBINOP, INSTPHI]
   then 1 else 0 }
  cvttoibc(s,i+1,slot+slotinc, result+bits)
  
  
  function reverse(s:seq.int)seq.int  @((+),_.s, empty:seq.int, arithseq(length.s, 0-1, length.s))



function bits(i:int,b:int) seq.int
    if i =0 then empty:seq.int else 
     bits(i-1,b / 2)+  (b mod 2)
     
Function astext(b:bitstream) seq.word
let s = reverse.@(+,bits(8),empty:seq.int,reverse.toseq.b)
    // @(+,toword, "",s)+ // astext(s,1,"",0)+"X"
     

function astext(   s:seq.int,i:int,result:seq.word,arg:int) seq.word 
    if arg=0 then
      if subseq(s,i,i+3)=[1,1,0,0] then
        astext(s,i+4,result+"&br",arg-1)
      else result
    else  
     if i+5 > length.s then result+"early end" else
    if arg=-2 then
        let argvalue = value(s,i,i+4)
         astext(s,i+6,result+toword.argvalue,argvalue)
    else 
    if s_(i+5) = 1 then astext(s,i+6,result+toword.value(s,i,i+4)+"_",arg) else astext(s,i+6,result+toword.value(s,i,i+4),arg-1) 
    

Function cvttoibc(d:seq.seq.int) internalbc
cvttoibc(d,1,1,emptyinternalbc)

function value(s:seq.int,i:int,j:int) int
    if i > j then 0 else s_i+ 2 * value(s,i+1,j)    
   
Function checkibc(offset:int,d:seq.seq.int) bitstream
// PROFILE. //
  let z = cvttoibc(d,1,1,emptyinternalbc)
  tobitstream(offset,z)
  
   let k = addbodyrecords(offset, emptyx, 4, offset, d, 1)
   let a = align.k
   let b = align.tobitstream(offset,z)
   let a1 = @(+,bits(8),empty:seq.int,reverse.toseq.b)
   let a2 = @(+,bits(8),empty:seq.int,reverse.toseq.b)
   assert a1 = a2 report "FAIL X" +toword.length.a1 +toword.length.a2+"START"+@(+,aaa,"",d)
     k

function aaa(s:seq.int) seq.word " &br["+ @(seperator(","),toword,"",s)+"],"
