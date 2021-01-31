
   
Module pass2 

use breakblocks

use UTF8

use bits

use seq.char

use otherseq.int

use otherseq.seq.int

use seq.seq.int


use set.int

use otherseq.mytype

use seq.mytype

use real

use standard

use otherseq.symbol

use seq.seq.seq.symbol

use seq.seq.symbol

use worddict.seq.symbol

use seq.symbol

use set.symbol

use symbol

use otherseq.word

use seq.seq.word

use set.seq.word

use seq.int

use set.word

function firstopt(p:program, rep:symbol, code:seq.symbol, alltypes:typedict)program
 let nopara = nopara.rep
    if isempty.removeoptions.code then
    map(p, rep,code)
 else
   let pdict = addpara(emptyworddict:worddict.seq.symbol, nopara)
   let code2 = code.yyy(p, code, 1, empty:seq.symbol, nopara + 1, pdict,true)
   let s = symbol(fsig.rep, module.rep, returntype.rep)
   let a = breakblocks(p, code2, s, alltypes)
   let a2 = code.yyy(p, a, 1, empty:seq.symbol, nopara + 1, pdict,true)
     addf(p, s, a2 )
    


function print(s:seq.int)seq.word s @ +("", toword.@e)

function var(i:int)symbol Local.i

function var(w:word)symbol Local.w

function addpara(map:worddict.seq.symbol, i:int)worddict.seq.symbol
 if i ≤ 0 then map
 else
  let v = var.i
   addpara(add(map, toword.i, [ v]), i - 1)

function addlooplocals(map:worddict.seq.symbol, firstvar:int, nextvar:int, nopara:int, i:int)worddict.seq.symbol
 if i = nopara then map
 else
  addlooplocals(replace(map, toword(firstvar + i), [ var(nextvar + i)]), firstvar, nextvar, nopara, i + 1)

use interpreter

use words

function yyy(p:program, org:seq.symbol, k:int, result:seq.symbol, nextvar:int, map:worddict.seq.symbol,papply:boolean)expandresult
 if k > length.org then expandresult(nextvar, result)
 else
  let sym = org_k
  let len = length.result
   if isconst.sym then yyy(p, org, k + 1, result + sym, nextvar, map, papply)
   else  if isspecial.sym then
   if fsig.sym = "BLOCK 3"then
    let t = backparse(result, len, 3, empty:seq.int) + [ len + 1]
     let condidx = t_2 - 4
     let cond = result_condidx
  let newresult=    if not.isbr.result_(condidx + 3)  then
        result + sym 
      else
       if cond=Litfalse   then
         let keepblock=value.result_(condidx + 2)
         subseq(result, 1, condidx - 1) +subseq(result, t_keepblock, t_(keepblock + 1) - 2)
        else if cond=Littrue   then
         let keepblock=value.result_(condidx + 1)
         subseq(result, 1, condidx - 1) +subseq(result, t_keepblock, t_(keepblock + 1) - 2)
         else  
         result+sym
         yyy(p, org, k + 1, newresult, nextvar, map, papply)
    else if // isdefine //(fsig.sym)_1 = "DEFINE"_1 then
    let thelocal =(fsig.sym)_2
      if len > 0 ∧ (isconst.result_len ∨ islocal.result_len)then
      yyy(p, org, k + 1, subseq(result, 1, length.result - 1), nextvar, replace(map, thelocal, [ result_len]),papply)
      else
       yyy(p, org, k + 1, result + Define.toword.nextvar, nextvar + 1, replace(map, thelocal, [ var.nextvar]),papply)
    else if isloopblock.sym then
    let nopara = nopara.sym - 1
     let firstvar = value.result_len
      yyy(p, org, k + 1, subseq(result, 1, len - 1) + Lit.nextvar + sym, nextvar + nopara, addlooplocals(map, firstvar, nextvar, nopara, 0),papply)
    else if(fsig.sym)_1 = "RECORD"_1 then
    let nopara = nopara.sym
     let args = subseq(result, len + 1 - nopara, len)
      if args @ ∧(true, isconst.@e)then
      yyy(p, org, k + 1, subseq(result, 1, len - nopara) + Constant2(args + sym), nextvar, map, papply)
      else yyy(p, org, k + 1, result + sym, nextvar, map, papply)
    else if(module.sym)_1 = "local"_1 then
    let t = lookup(map,(fsig.sym)_1)
      if isempty.t then yyy(p, org, k + 1, result + sym, nextvar, map, papply)
      else yyy(p, org, k + 1, result + t_1, nextvar, map, papply)
    else if(module.sym)_1 = "para"_1 then
    let sym2 = Local.(module.sym)_2
     let t = lookup(map,(fsig.sym2)_1)
      if isempty.t then yyy(p, org, k + 1, result + sym2, nextvar, map, papply)
      else yyy(p, org, k + 1, result + t_1, nextvar, map, papply)
    else if len > 2 ∧  result_(len - 2) = NotOp ∧ fsig.sym = "BR 3"then
    yyy(p, org, k + 1, subseq(result, 1, len - 3) + [ result_len, result_(len - 1), Br], nextvar, map, papply)
    else yyy(p, org, k + 1, result + sym, nextvar, map, papply)
   else if papply &and (fsig.sym)_1 ∈ "apply3"then applycode4(p, org, k, result, nextvar, map, papply)
    else if papply &and (fsig.sym)_1 ∈ "apply5"then applycode5(p, org, k, result, nextvar, map, papply)
   else
    let nopara = nopara.sym
    let dd = code.lookupcode(p, sym)
    let options=getoption.dd
        if first."COMPILETIME"  ∈ options &and subseq(result,len-nopara+1,len) @ &and(true,isconst.@e)   then 
           let newcode= interpret(subseq(result,len-nopara+1,len)+sym)
         let newconst=if length.newcode > 1 then Constant2.newcode else first.newcode
           yyy(p, org, k + 1, result >> nopara + newconst, nextvar, map, papply)
     else if  "INLINE"_1 ∈ options  &or first."VERYSIMPLE" ∈ options then
     let code = removeoptions.dd
       if isempty.code then yyy(p, org, k + 1, result + sym, nextvar, map, papply)
       else inline(p, org, k, result, nextvar, nopara, code, map, options,papply)
     else  if nopara = 1 &and isconst.result_len then
      // one constant parameter //
       if sym = symbol("toword(int)","UTF8","word")then
       yyy(p, org, k + 1, subseq(result, 1, length.result - 1) + Word.(fsig.last.result)_1, nextvar, map, papply)
       else  if fsig.sym = "decode(char seq encoding)" ∧ module.sym = "char seq encoding"then
       let arg1 = result_len
         if module.arg1 = "$word"then
         let a1 = tointseq.decodeword.(fsig.arg1)_1 @ +(empty:seq.symbol, Lit.@e)
          let d = Constant2([ Stdseq, Lit.length.a1] + a1 + Record.constantseq(length.a1 + 2,"int"_1))
           yyy(p, org, k + 1, subseq(result, 1, len - 1) + d, nextvar, map, papply)
         else yyy(p, org, k + 1, result + sym, nextvar, map, papply)
          else yyy(p, org, k + 1, result + sym, nextvar, map, papply)
      else  if nopara=2 &and last.module.sym = "seq"_1 &and isconst.result_len &and isconst.result_(len - 1) 
        ∧ ( fsig.sym  = "_(" + subseq(module.sym, 1, length.module.sym - 1) + "seq, int)") then 
       // two parameters with constant args //
       // should add case of IDXUC with record as first arg //
         // two parameters with constant args //
          // assert   module.sym &in ["word seq", "char seq","int seq","Tpair seq"] 
          report "here pass2"+print.sym //
        let idx = value.result_len
         let arg1 = result_(len - 1)
          if module.arg1 = "$words" ∧ between(idx, 1, length.fsig.arg1)then
          yyy(p, org, k + 1, subseq(result, 1, len - 2) + Word.(fsig.arg1)_idx, nextvar, map, papply)
          else if isrecordconstant.arg1 ∧ ((constantcode.arg1)_1 = Lit.0 ∨ (constantcode.arg1)_1 = Lit.1)
          ∧ between(idx, 1, length.constantcode.arg1 - 2)then
          yyy(p, org, k + 1, subseq(result, 1, len - 2) + (constantcode.arg1)_(idx + 2), nextvar, map, papply)
          else yyy(p, org, k + 1, result + sym, nextvar, map, papply)
        else yyy(p, org, k + 1, result + sym, nextvar, map, papply)


function inline(p:program, org:seq.symbol, k:int, result:seq.symbol, nextvar:int, nopara:int, code:seq.symbol, map:worddict.seq.symbol, options:seq.word,papply:boolean)expandresult
 if length.code = 1 ∧ code = [ var.1] ∧ nopara = 1 then
 // function just returns result // yyy(p, org, k + 1, result, nextvar, map,papply)
 else
  let len = length.result
  let t = backparse(result, len, nopara, empty:seq.int) + [ len + 1]
   assert length.t = nopara + 1 report"INLINE PARA PROBLEM"
   let new = if"STATE"_1 ∉ options ∧ issimple(p, nopara, code)then
   let pmap = simpleparamap(result, t, emptyworddict:worddict.seq.symbol, nopara)
     yyy(p, code, 1, empty:seq.symbol, nextvar, pmap,papply)
   else expandinlineX(result, t, emptyworddict:worddict.seq.symbol, nopara, empty:seq.symbol, nextvar, code, p,papply)
    yyy(p, org, k + 1, subseq(result, 1, t_1 - 1) + code.new, nextvar.new, map,papply)

function simpleparamap(s:seq.symbol, t:seq.int, pmap:worddict.seq.symbol, i:int)worddict.seq.symbol
 if i = 0 then pmap
 else
  simpleparamap(s, t, add(pmap, toword.i, subseq(s, t_i, t_(i + 1) - 1)), i - 1)

function expandinlineX(s:seq.symbol, t:seq.int, pmap:worddict.seq.symbol, i:int, newcode:seq.symbol, nextvar:int, 
inlinecode:seq.symbol, p:program,papply:boolean)expandresult
 // when i > 0 then assigning parameters to new local variables //
 if i = 0 then
 let r = yyy(p, inlinecode, 1, empty:seq.symbol, nextvar, pmap,papply)
   expandresult(nextvar.r, newcode + code.r)
 else
  expandinlineX(s, t, add(pmap, toword.i, [ var.nextvar]), i - 1, subseq(s, t_i, t_(i + 1) - 1) + Define.toword.nextvar + newcode, nextvar + 1, inlinecode, p,papply)




function replace(s:seq.symbol, start:int, length:int, value:seq.symbol)seq.symbol
 subseq(s, 1, start - 1) + value + subseq(s, start + length, length.s)

function adddefines2(s:seq.symbol, t:seq.int, i:int, nopara:int, newcode:seq.symbol, nextvar:int)seq.symbol
 if i > nopara then newcode
 else
  adddefines2(s, t, i + 1, nopara, newcode + subseq(s, t_i, t_(i + 1) - 1)
  + Define.toword(nextvar + i - 1), nextvar)

type expandresult is record nextvar:int, code:seq.symbol

function definepara(code:seq.symbol, t:seq.int, i:int, nextvar:int, newcode:seq.symbol)seq.symbol
 if i = 0 then newcode
 else
  definepara(code, t, i - 1, nextvar - 1, subseq(code, t_i, t_(i + 1) - 1) + Define.toword.nextvar + newcode)

function dfg(s:symbol)seq.word
 if islocal.s then"%"
 else
  let a = last.module.s
   [ a, if a ∈ "$define local"then first."?"else first.fsig.s]


function subapply( thunk:seq.symbol,    e:symbol,i:symbol,acc:symbol ) seq.symbol
  thunk @ +(empty:seq.symbol,
   if  length.module.@e &le 1 &or last.module.@e &ne "builtin"_1  then @e 
        else if  fsig.@e="@e"  then e
        else if  fsig.@e="@i"  then i
        else if fsig.@e="@acc"  then acc
        else @e)
  
function substitute (s:seq.symbol,old:seq.symbol,new:seq.symbol) seq.symbol
     s @ +(empty:seq.symbol, let i=findindex( @e,old)
        if between(i,1,length.old) then new_i   else @e)
        

function simpleAcc(thunk:seq.symbol,resulttype:seq.word,lastvar:int,seqelement:symbol
,newmasteridx:symbol) breakresult
   let acc = Local(lastvar +1)
   let masteridx1 = Local(lastvar +2)
   let x2=   subapply(thunk,seqelement,masteridx1,acc ) 
    breakresult([ Lit.1,Lit.lastvar,Loopblock("ptr," + resulttype + ", int,  int)")],
        x2+ [  newmasteridx, continue.3],
     [acc],
     lastvar+3,masteridx1)
 

          
type compoundAC is record state:word,result:seq.symbol,fldno:int 

    
function chkAcc(a:compoundAC,next:symbol,fldvar:seq.symbol) compoundAC
    let state=state.a 
     let newstate=  if state="start"_1 then
        if next=Local.1 then "local1"_1
        else  "start"_1
     else if state="local1"_1 then 
        if  not.islit.next then "fail"_1
        else   
         "idx"_1
     else if state ="idx"_1 then if next &in [IdxInt,IdxReal,IdxPtr] then "start"_1 else "fail"_1
      else "fail"_1
     let newresult=if newstate="start"_1 then
         if state="start"_1 then  result.a+next
         else   result.a +   fldvar_(fldno.a +1)
         else result.a    
    compoundAC(newstate,newresult, if islit.next then value.next else fldno.a)
   
 /function breakAccumalator5(p:program,thunk:seq.symbol,resulttype:seq.word,lastvar:int,seqelement:symbol
,newmasteridx:symbol,papply:boolean,thunkplaceholders:seq.symbol) breakresult
 //  lastvar+1 to lastvar+nopara.last.code are accumalators //
 //  lastvar+1+nopara.last.code lastvar+nopara.last.code+nopara.accfunc-1 are location of parameters for lastvar //
 let accfunc=last.thunk
  let  ttt=lookupcode(p,last.thunk)
let code=removeoptions.code.ttt
if isempty.code &or not.isrecord.last.code then issimple
else 
   let noAccumlators=nopara.last.code
       let fldnames= paratypes.last.code @+("", merge([toword.@i]+typerep.@e))
      let fldsyms= fldnames @+(empty:seq.symbol,Local.@e)
      let t5=code  @ chkAcc(compoundAC("start"_1,empty:seq.symbol,0),@e,fldsyms)
   if  state.t5="fail"_1   then issimple
 else  
  let x= fldnames @ add(emptyworddict:worddict.seq.symbol ,   @e, [Local.( lastvar+@i)]) 
  let masteridx=lastvar+noAccumlators+1
  let pmap= paratypes.accfunc << 1 @ add(x , toword.(@i+1), [Local.( masteridx+@i)]) 
  let nextvar=   masteridx+nopara.accfunc 
   let r = yyy(p, result.t5, 1, empty:seq.symbol, nextvar, pmap,papply)
    let thunkcode=   substitute(subseq(thunk,2,length.thunk-1),thunkplaceholders,[seqelement,Lit.0 ,Local.masteridx])   
      +
        arithseq(nopara.accfunc-1,-1,nextvar-1) @+( empty:seq.symbol, 
         Define.toword(@e))+code.r + newmasteridx+continue.(noAccumlators+2)    
    let orgacc=   nextvar.r
   let loopcode = arithseq(nopara.last.code,4,2) @+  ([Define.orgacc], [Local.orgacc]+ subseq(code,@e,@e+1))+
    [ Lit.1,Lit.lastvar,Loopblock("ptr," + subseq(fsig.last.code,3,length.fsig.last.code-1) + ", int,  int)")]
   let finalcode= arithseq(noAccumlators,1,lastvar+1) @ +(empty:seq.symbol,(Local.@e))+last.code
    breakresult(loopcode,thunkcode,finalcode,orgacc+1,Local.masteridx)
 
type breakresult is record loopcode:seq.symbol,thunkcode:seq.symbol,finalcode:seq.symbol,nextvar:int,
     masteridx:symbol

function  issimple breakresult breakresult(empty:seq.symbol,empty:seq.symbol,empty:seq.symbol,0,Lit.0)

function print(b:breakresult) seq.word
   "loopcode:"+print.loopcode.b
   +EOL+"thunkcode:"+print.thunkcode.b
  +EOL+"finalcode:"+print.finalcode.b
  +EOL+"nextvar:"+print.nextvar.b
   
function applycode5(p:program, org:seq.symbol, k:int, code:seq.symbol, nextvar:int, map:worddict.seq.symbol,papply:boolean)expandresult
  let totallength = nextvar + 1
   let seqtype= Local(nextvar + 2)
 let Defineseqtype = Define(nextvar+2)
 let Definenewmasteridx = Define(nextvar + 3)
 let newmasteridx = Local(nextvar + 3)
 let Defineseqelement = Define(nextvar + 4)
 let seqelement = Local(nextvar + 4)
 let Defineinitacc=Define(nextvar + 5)
 let initacc=Local(nextvar + 5)
 let theseq = Local(nextvar + 6)
 let lastUsed=nextvar+6
  let applysym = org_k
  let ds=(typerep.parameter.(paratypes.applysym)_2)_1
  let seqelementkind =
  if ds &in "int real" then ds else 
  if ds &in "bit byte" then "int"_1 else "ptr"_1
  let resulttype =  (paratypes.applysym)_1 
  let exitstart=backparse(code, length.code , 1, empty:seq.int)_1
  let exitexp=subseq(code,exitstart,length.code)
  let t = backparse(code, exitstart - 1, 1, empty:seq.int)
  let thunk0 = subseq(code,t_1,exitstart-1) 
   let accfunc = last.thunk0
  let thunkplaceholders=subseq(code,t_1-3,t_1-1)
  let initseq=code_(t_1-4)
  let isnoop=
   exitexp=[Litfalse] 
   &and length.thunk0=6 
   &and first.fsig.accfunc="+"_1 
   &and isrecord.thunk0_5
   &and  thunk0 >> 2 =[thunkplaceholders_2,Lit.0,Lit.1,thunkplaceholders_1]  
   &and   code_(t_1-5) =Constant2.Emptyseq  
  if isnoop then   yyy(p, org, k + 1, code >> 12 +initseq, nextvar, map,papply)
   else
       let part1 = subseq(code, 1, t_1 - 5) + [Defineinitacc,initseq, Lit.1, IdxInt, Define.totallength
       ,initseq,initacc] 
 let checkCompound = // if typerep.resulttype = " ptr"  &and length.thunk0 > 2 &and first.thunk0=thunkplaceholders_2
     then    may have compound accumalator  
        breakAccumalator5(p ,thunk0,typerep.resulttype, lastUsed,seqelement,newmasteridx,papply,thunkplaceholders) 
      else // issimple 
 let  codeparts=   if nextvar.checkCompound=nextvar.issimple then 
  \\ simple acc \\
   let acc = Local(lastUsed +1)
   let masteridx1 = Local(lastUsed +2)
   breakresult([ Lit.1,Lit.lastUsed,Loopblock("ptr," + typerep.resulttype + ", int,  int)")],
        substitute(thunk0,thunkplaceholders,[seqelement,acc,masteridx1])+ [  newmasteridx, continue.3],
     [acc],
     lastUsed+3,masteridx1)
   else checkCompound 
        let masteridx=masteridx.codeparts
      let exitexp2=if exitexp=[Litfalse] then empty:seq.symbol else   
       substitute( exitexp,thunkplaceholders,[ seqelement,// needs attention // Lit.0,masteridx] )
       +[ Lit.2 ,Lit.3, Br, Local.totallength , Lit.1,PlusOp,Exit,newmasteridx,Exit,  Block(typeint,3)]
      let thunkcode=   if isempty.exitexp2 then thunkcode.codeparts
           else let a= thunkcode.codeparts
              a >> 2 + exitexp2 + last.a
     let kk =  
    //  loop(seq, acc, masteridx)//
    // 1 // loopcode.codeparts+  
    // 2  if  masteridx > totallength  then exit // 
        [masteridx,Local.totallength,  GtOp, Lit.3, Lit.4, Br]+ 
    // 3 // finalcode.codeparts +[ Exit,
      // 4 else  let newmasteridx = masteridx + 1, 
    let sequenceele = seq_(idx)
     continue(thseqeq,thunk,newmasteridx) //
         masteridx, Lit.1, PlusOp, Definenewmasteridx,
         theseq, Lit.0,IdxInt,Defineseqtype ,
          seqtype, Lit.0, EqOp ,Lit.2,Lit.3, Br,
         theseq, newmasteridx, Idx.seqelementkind, Exit]+ 
         ( if ds &in "int real ptr"   then
              [ theseq, masteridx, Callidx.seqelementkind ,   Exit,
         Block(mytype.[seqelementkind],3)]      
         else 
          [seqtype,     Lit.1, EqOp ,Lit.4,Lit.5, Br,
             theseq, masteridx ,Lit.-1,PlusOp ]+ packedtype( ds)+[Exit,
           theseq, masteridx, Callidx.seqelementkind ,   Exit,
         Block(mytype.[seqelementkind],5)])      
        +    [  Defineseqelement, theseq]
        + thunkcode+
 [   Block(resulttype, 4)]
       yyy(p, org, k + 1, part1 + kk, nextvar.codeparts, map,papply)
   

 yyy(p, org, k + 1, code, nextvar , map,papply)
 
 for(e &in s,acc=empty:seq.T,i,false) acc+e 
   
function applycode4(p:program, org:seq.symbol, k:int, code:seq.symbol, nextvar:int, map:worddict.seq.symbol,papply:boolean)expandresult
  let totallength = nextvar + 1
 let applysym = org_k
 let ds=(typerep.parameter.(paratypes.applysym)_1)_1
//   assert  code_-1 =Lit.0   report  print.code_-1+ ds  +print.org //
 let seqelementkind =if ds &in "int real" then ds else 
  if ds &in "bit byte" then "int"_1 else "ptr"_1
 let resulttype = [(module.applysym)_1]
// let descleft = Lit.-2 //
 let seqtype= Local(nextvar + 2)
 let Defineseqtype = Define(nextvar+2)
 let Definenewmasteridx = Define(nextvar + 3)
 let newmasteridx = Local(nextvar + 3)
 let Defineseqelement = Define(nextvar + 4)
 let seqelement = Local(nextvar + 4)
 let theseq = Local(nextvar + 5)
  let exitstart=backparse(code, length.code , 1, empty:seq.int)_1
  let exitexp=subseq(code,exitstart,length.code)
  let sym = code_(exitstart-1)
 let t = backparse(code, exitstart - 2, nopara.sym, empty:seq.int)
 let thunk0 = subseq(code,t_1,exitstart-1) 
// assert false report "XXX"+thunk0 @ +("", dfg.@e)+EOL+thunk0 @+("",print.@e)+EOL+toword.length.thunk0
//  let checknoop = if length.thunk0 &in[ 10,6] &and exitexp=[Lit.0] 
     ∧ thunk0 @ +("", dfg.@e)  &in[ "builtin @acc $define ? builtin @e $define ? % $int 0 $int 1 % $record RECORD seq +"
   ,"builtin @acc $int 0 $int 1 builtin @e $record RECORD seq +"]
   then
      let b2 = backparse(code, t_1 - 1, 2, empty:seq.int)
     if subseq(code, b2_1, b2_2 - 1) = [ Constant2.Emptyseq]then subseq(code, 1, b2_1 - 1)
    else empty:seq.symbol
  else empty:seq.symbol
   if not.isempty.checknoop then   yyy(p, org, k + 1, checknoop, nextvar, map,papply)
   else
       let part1 = subseq(code, 1, t_1 - 1) + [ Lit.1, IdxInt, Define.totallength]
      let codeparts= simpleAcc(thunk0,resulttype,value.theseq,seqelement,newmasteridx )
     let masteridx=masteridx.codeparts
      let exitexp2=if exitexp=[Lit.0] then empty:seq.symbol else   
       subapply( exitexp,seqelement,masteridx,Lit.0 )
       +[ Lit.2 ,Lit.3, Br, Local.totallength , Lit.1,PlusOp,Exit,newmasteridx,Exit,  Block(typeint,3)]
  //   assert false report "JJ"+print.exitexp2+"??"+print.exitexp   //
      let thunkcode=   if isempty.exitexp2 then thunkcode.codeparts
           else let a= thunkcode.codeparts
              a >> 2 + exitexp2 + last.a
     let kk =  
    //  loop(seq, acc, masteridx)//
    // 1 // loopcode.codeparts+  
    // 2  if  masteridx > totallength  then exit // 
        [masteridx,Local.totallength,  GtOp, Lit.3, Lit.4, Br]+ 
    // 3 // finalcode.codeparts +[ Exit,
      // 4 else  let newmasteridx = masteridx + 1, 
    let sequenceele = seq_(idx)
     continue(thseqeq,thunk,newmasteridx) //
         masteridx, Lit.1, PlusOp, Definenewmasteridx,
         theseq, Lit.0,IdxInt,Defineseqtype ,
          seqtype, Lit.0, EqOp ,Lit.2,Lit.3, Br,
         theseq, newmasteridx, Idx.seqelementkind, Exit]+ 
         ( if ds &in "int real ptr"   then
              [ theseq, masteridx, Callidx.seqelementkind ,   Exit,
         Block(mytype.[seqelementkind],3)]      
         else 
          [seqtype,     Lit.1, EqOp ,Lit.4,Lit.5, Br,
             theseq, masteridx ,Lit.-1,PlusOp ]+ packedtype( ds)+[Exit,
           theseq, masteridx, Callidx.seqelementkind ,   Exit,
         Block(mytype.[seqelementkind],5)])      
        +    [  Defineseqelement, theseq]
        + thunkcode+
 [   Block(mytype.resulttype, 4)]
   //  assert length.finalcode.codeparts=1 report  "check apply"+ print.codeparts+EOL+print.(part1+kk)
   //    yyy(p, org, k + 1, part1 + kk, nextvar.codeparts, map,papply)
   
   // zz &in "seq char mytype int token templatepart  myinternaltype UTF8 encoding llvmtype
    Lcode2 slotrecord mapele liblib parc attribute2 prettyresult internalbc"  //
    
        
         
   function  packedtype( ds:word) seq.symbol
             let GEP=symbol("GEP(ptr seq, int)","internal","ptr")
        if ds &in "bit" then   
                [symbol("extractbit(int seq,int)","internal","int")]  
     else  if ds &in  "byte" then
               [symbol("extractbyte(int seq,int)","internal","int")]
      else  // element represented by multiple words //
         [    Lit.toint.ds,MultOp, Lit.2, PlusOp ,GEP]
      


function maxvarused(code:seq.symbol)int maxvarused(code, 1, 0)

function maxvarused(code:seq.symbol, i:int, lastused:int)int
 if i > length.code then lastused
 else
  let s = code_i
   maxvarused(code
   , i + 1
   , max(lastused, if abstracttype.modname.s = "local"_1 then toint.(fsig.s)_1
   else if abstracttype.modname.s = "$define"_1 then toint.(fsig.s)_2 else 0))

Function depthfirst(processed:program, knownsymbols:program, alltypes:typedict, s:symbol)program depthfirst(knownsymbols, alltypes, 1, [ s], processed, code.lookupcode(knownsymbols, s), s)

function depthfirst(knownsymbols:program, alltypes:typedict, i:int, pending:seq.symbol, processed:program, code:seq.symbol, s:symbol)program
 if i > length.code then firstopt(processed, s, code, alltypes)
 else
  let sym = code_i
  let sym2 = basesym.sym
  let newprg =
   if  isconst.sym2 ∨ isspecial.sym2   &or sym2 ∈ pending then processed
   else
     let r = lookupcode(processed, sym)
      if isdefined.r then processed
     else
      let rep2 = lookupcode(knownsymbols, sym2)
       if length.code.rep2 > 0 then 
       depthfirst(knownsymbols, alltypes, 1, pending + sym2, processed, code.rep2, sym2)else processed
       depthfirst(knownsymbols, alltypes, i + 1, pending, newprg, code, s)

________________________________
 
 
function addf(p:program,s:symbol,code0:seq.symbol) program
let options = getoption.code0
   let code=removeoptions.code0
    let fsig=fsig.s
let newoptions=  if fsig = "∈(int, int seq)"
  ∨ fsig = "∈(word, word seq)"
  ∨ fsig = "_(int seq, int)"
  ∨ fsig = "_(word seq, int)"then
  ""
  else
    let state=state100(code ,p,s)
    options+(  if hasstate.state &and  "STATE"_1 &nin options  then "STATE" else "" )
    +if length.code < 20 &and not.callsself.state &and "NOINLINE"_1 &nin options then "INLINE" else ""
       map(p, s, if newoptions = ""then code else code + Words.newoptions + Optionsym
 )
 


// statebit is set on option so that adding an option doesn't auto add a inline bit //

Function issimple(p:program, nopara:int, code:seq.symbol)boolean
 between(length.code, 1, 15) ∧ (nopara = 0 ∨ checksimple(p, code, 1, nopara, 0))


function checksimple(p:program, code:seq.symbol, i:int, nopara:int, last:int)boolean
 // check that the parameters occur in order and they all occur exactly once //
 // Any op that may involve state must occur after all parameters //
 // should also check for loopblock //
 if i > length.code then last = nopara
 else
  let rep = code_i
   if islocal.rep then
   let parano = value.rep
     if parano = last + 1 &and (nopara &ne parano &or not.hasstate.state100(subseq(code,1,i-1),p,rep))
           then checksimple(p, code, i + 1, nopara, last + 1)else false
   else checksimple(p, code, i + 1, nopara, last)

---------------------------

Function pass2(placehold:program, alltypes:typedict)program 
let bin0=  toseq.toset.placehold @ filterp(filterp(emptyprogram,emptyprogram ), @e
,     code.lookupcode(placehold,@e),alltypes)
let bin=  toseq.toset.complex.bin0 @ filterp(filterp(emptyprogram,simple.bin0 ), @e
,     code.lookupcode(complex.bin0,@e),alltypes)
  //  assert false report checkt( bin0)
           assert false report print.length.toseq.toset.complex.bin + print.length.toseq.toset.simple.bin  
  //     toseq.toset.complex.bin   @ depthfirst(simple.bin, placehold, alltypes, @e)

/function checkt(s:filterp) seq.word
  let t1 =toseq.toset.complex.s @+(empty:seq.symbol,    let t=code.lookupcode(complex.s,@e)
     if length.t < 20 then t else empty:seq.symbol)
   "CHECK"+toseq.asset.t1 @+("" ,  //  if isconst.@e &or isspecial.@e &or islocal.@e then "" else   print.@e ) //
   if hasunknown.state100([@e],simple.s,Lit.0) then  print.@e else "")
    

 toseq.toset.complex.bin  @ xxx(simple.bin,alltypes,@e)
  
type filterp is  record complex:program,simple:program 
 
function  filterp(p:filterp,s:symbol,code:seq.symbol, alltypes:typedict) filterp
  let complex= complex.p let simple= simple.p  
 let options=getoption.code 
 if isempty.code &or  "BUILTIN"_1 &in options &or "VERYSIMPLE"_1 &in options 
    &or "ABSTRACTBUILTIN"_1 &in options then
     filterp(complex,map(simple,s,code) ) 
 else 
     if length.code < 30 then
        // 10 is choosen to be min size of code with apply3 //
      let nopara=nopara.s
      let pdict = addpara(emptyworddict:worddict.seq.symbol, nopara)
      let code2 = code.yyy(simple, code, 1, empty:seq.symbol, nopara + 1, pdict,false)
      if  (length.code2=3 &and code2_1=Local.1 &and fsig(code2_3)_1 &in "IDX2"  &and isconst.code2_2) 
      &or (length.code2=1 &and nopara=1 &and  code2_1=Local.1 )  then 
        filterp(complex,map(simple,s,code2+[ Words."VERYSIMPLE", Optionsym]) )
     else
         if  hasunknown.state100(removeoptions.code2 ,simple,s)  then 
            filterp( addf  (complex, s, code),simple ) 
        else 
            filterp( complex, firstopt(simple,s,code2,alltypes))
     else  
      filterp(map(complex,s,code),simple )
      
      

         
     

 
  function  xxx(p:program,alltypes:typedict, s:symbol) program
        let code=code.lookupcode(p,s)
        if isempty.code then p
        else 
        firstopt(p , s, code, alltypes)     

Function uses(p:program, roots:set.symbol)set.symbol uses(p, empty:set.symbol, roots)


Function defines(p:program, roots:set.symbol)seq.symbol toseq.roots @ +(empty:seq.symbol, 
if isconstantorspecial.@e ∨   isabstract.modname.@e then empty:seq.symbol
 else [@e])
 


function uses(p:program, processed:set.symbol, toprocess:set.symbol)set.symbol
 if isempty.toprocess then processed
 else
  let q = asset(toseq.toprocess @ +(empty:seq.symbol, let d = code.lookupcode(p, @e)
  if isempty.d then constantcode.@e else d))
   uses(p, processed ∪ toprocess, q - processed)

