
   
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
   let code2 = code.yyy(p, code, 1, empty:seq.symbol, nopara + 1, pdict)
   let options = caloptions(p, code2, nopara, module.rep, fsig.rep)
   let s = symbol(fsig.rep, module.rep, returntype.rep)
   let a = breakblocks(p, code2, s, alltypes)
   let a2 = code.yyy(p, a, 1, empty:seq.symbol, nopara + 1, pdict)
    map(p, s, addoptions(a2, options))

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

function yyy(p:program, org:seq.symbol, k:int, result:seq.symbol, nextvar:int, map:worddict.seq.symbol)expandresult
 if k > length.org then expandresult(nextvar, result)
 else
  let sym = org_k
  let len = length.result
   if isconst.sym then yyy(p, org, k + 1, result + sym, nextvar, map)
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
         yyy(p, org, k + 1, newresult, nextvar, map)
    else if // isdefine //(fsig.sym)_1 = "DEFINE"_1 then
    let thelocal =(fsig.sym)_2
      if len > 0 ∧ (isconst.result_len ∨ islocal.result_len)then
      yyy(p, org, k + 1, subseq(result, 1, length.result - 1), nextvar, replace(map, thelocal, [ result_len]))
      else
       yyy(p, org, k + 1, result + Define.toword.nextvar, nextvar + 1, replace(map, thelocal, [ var.nextvar]))
    else if isloopblock.sym then
    let nopara = nopara.sym - 1
     let firstvar = value.result_len
      yyy(p, org, k + 1, subseq(result, 1, len - 1) + Lit.nextvar + sym, nextvar + nopara, addlooplocals(map, firstvar, nextvar, nopara, 0))
    else if(fsig.sym)_1 = "RECORD"_1 then
    let nopara = nopara.sym
     let args = subseq(result, len + 1 - nopara, len)
      if args @ ∧(true, isconst.@e)then
      yyy(p, org, k + 1, subseq(result, 1, len - nopara) + Constant2(args + sym), nextvar, map)
      else yyy(p, org, k + 1, result + sym, nextvar, map)
    else if(module.sym)_1 = "local"_1 then
    let t = lookup(map,(fsig.sym)_1)
      if isempty.t then yyy(p, org, k + 1, result + sym, nextvar, map)
      else yyy(p, org, k + 1, result + t_1, nextvar, map)
    else if(module.sym)_1 = "para"_1 then
    let sym2 = Local.(module.sym)_2
     let t = lookup(map,(fsig.sym2)_1)
      if isempty.t then yyy(p, org, k + 1, result + sym2, nextvar, map)
      else yyy(p, org, k + 1, result + t_1, nextvar, map)
    else if len > 2 ∧  result_(len - 2) = NotOp ∧ fsig.sym = "BR 3"then
    yyy(p, org, k + 1, subseq(result, 1, len - 3) + [ result_len, result_(len - 1), Br], nextvar, map)
    else yyy(p, org, k + 1, result + sym, nextvar, map)
   else if(fsig.sym)_1 ∈ "apply3"then applycode4(p, org, k, result, nextvar, map)
   else
    let nopara = nopara.sym
    let dd = code.lookupcode(p, sym)
    let options=getoption.dd
   //   if first."BUILTIN"  ∈ options &and nopara=2 &and subseq(result,len-nopara+1,len) @ &and(true,isconst.@e)   then 
        opttwoopbuiltin(p, org, k, result, nextvar, map, sym)
     else //
       if first."COMPILETIME"  ∈ options &and subseq(result,len-nopara+1,len) @ &and(true,isconst.@e)   then 
           let newcode= interpret(subseq(result,len-nopara+1,len)+sym)
         let newconst=if length.newcode > 1 then Constant2.newcode else first.newcode
           yyy(p, org, k + 1, result >> nopara + newconst, nextvar, map)
     else if  "INLINE"_1 ∈ options  &or first."VERYSIMPLE" ∈ options then
     let code = if last.dd = Optionsym then subseq(dd, 1, length.dd - 2)else dd
       if isempty.code then yyy(p, org, k + 1, result + sym, nextvar, map)
       else inline(p, org, k, result, nextvar, nopara, code, map, getoption.dd)
     else if nopara = 0 ∨ nopara > 2 ∨ not.isconst.result_len then
     yyy(p, org, k + 1, result + sym, nextvar, map)
     else
      // one or two parameters with last arg being constant //
      if nopara = 1 then
      // one constant parameter //
       if sym = symbol("toword(int)","UTF8","word")then
       yyy(p, org, k + 1, subseq(result, 1, length.result - 1) + Word.(fsig.last.result)_1, nextvar, map)
       else  if fsig.sym = "makereal(word seq)" ∧ module.sym = "UTF8"then
        let arg1 = last.result
         if module.arg1 = "$words"then
         let x = Reallit.representation.makereal.fsig.arg1
           yyy(p, org, k + 1, subseq(result, 1, length.result - 1) + x, nextvar, map)
         else yyy(p, org, k + 1, result + sym, nextvar, map)
       else if fsig.sym = "merge(word seq)" ∧ module.sym = "words"then
       let arg1 = last.result
         if module.arg1 = "$words"then
         yyy(p, org, k + 1, subseq(result, 1, length.result - 1) + Word.merge.fsig.arg1, nextvar, map)
         else yyy(p, org, k + 1, result + sym, nextvar, map)
       else if fsig.sym = "decode(char seq encoding)" ∧ module.sym = "char seq encoding"then
       let arg1 = result_len
         if module.arg1 = "$word"then
         let a1 = tointseq.decodeword.(fsig.arg1)_1 @ +(empty:seq.symbol, Lit.@e)
          let d = Constant2([ Stdseq, Lit.length.a1] + a1 + Record.constantseq(length.a1 + 2,"int"_1))
           yyy(p, org, k + 1, subseq(result, 1, len - 1) + d, nextvar, map)
         else yyy(p, org, k + 1, result + sym, nextvar, map)
       else if fsig.sym = "encode(char seq)" ∧ module.sym = "char seq encoding"then
       let arg1 = result_len
         if module.arg1 = "$constant"then
         let chseq = subseq(constantcode.arg1, 3, length.constantcode.arg1) @ +(empty:seq.int, value.@e)
           assert subseq(constantcode.arg1, 3, length.constantcode.arg1) @ ∧(true, islit.@e)report"const problem"
           let new = Word.encodeword(chseq @ +(empty:seq.char, char.@e))
            yyy(p, org, k + 1, subseq(result, 1, len - 1) + new, nextvar, map)
         else yyy(p, org, k + 1, result + sym, nextvar, map)
       else yyy(p, org, k + 1, result + sym, nextvar, map)
      else
       // two parameters with constant args //
       // should add case of IDXUC with record as first arg //
       if not.isconst.result_(len - 1)then yyy(p, org, k + 1, result + sym, nextvar, map)
       else
        // two parameters with constant args //
        if last.module.sym = "seq"_1
        ∧ (fsig.sym = "_(T seq, int)"
        ∨ fsig.sym
        = "_(" + subseq(module.sym, 1, length.module.sym - 1) + "seq, int)")then
        let idx = value.result_len
         let arg1 = result_(len - 1)
          if module.arg1 = "$words" ∧ between(idx, 1, length.fsig.arg1)then
          yyy(p, org, k + 1, subseq(result, 1, len - 2) + Word.(fsig.arg1)_idx, nextvar, map)
          else if isrecordconstant.arg1 ∧ ((constantcode.arg1)_1 = Lit.0 ∨ (constantcode.arg1)_1 = Lit.1)
          ∧ between(idx, 1, length.constantcode.arg1 - 2)then
          yyy(p, org, k + 1, subseq(result, 1, len - 2) + (constantcode.arg1)_(idx + 2), nextvar, map)
          else yyy(p, org, k + 1, result + sym, nextvar, map)
        else if fsig.sym = "+(word seq, word seq)" ∧ module.sym = "word seq"then
        let arg1 = result_(len - 1)
         let arg2 = result_len
          if module.arg1 = "$words" ∧ module.arg2 = "$words"then
          yyy(p, org, k + 1, subseq(result, 1, len - 2) + Words(fsig.arg1 + fsig.arg2), nextvar, map)
          else yyy(p, org, k + 1, result + sym, nextvar, map)
        else yyy(p, org, k + 1, result + sym, nextvar, map)

function opttwoopbuiltin(p:program, org:seq.symbol, k:int, result:seq.symbol, nextvar:int, map:worddict.seq.symbol, rep:symbol)expandresult
 let s = result
 let i = length.result + 1
  if isIdx.rep then
   assert false report "here in isIdx"
  let j = value.s_(i - 1)
   let x = s_(i - 2)
    if between(j, 0, length.constantcode.x - 1)then
    yyy(p, org, k + 1, subseq(result, 1, i - 3) + [(constantcode.x)_(j + 1)], nextvar, map)
    else yyy(p, org, k + 1, result + rep, nextvar, map)
   else  if fsig.rep = "+(int, int)"then
  yyy(p, org, k + 1, subseq(result, 1, i - 3)
   + Lit(value.s_(i - 2) + value.s_(i - 1)), nextvar, map)
 else  if fsig.rep = "-(int, int)"then
  yyy(p, org, k + 1, subseq(result, 1, i - 3)
   + Lit(value.s_(i - 2) - value.s_(i - 1)), nextvar, map)
 else  if fsig.rep = "*(int, int)"then
  yyy(p, org, k + 1, subseq(result, 1, i - 3)
   + Lit(value.s_(i - 2) * value.s_(i - 1)), nextvar, map)
 else  if fsig.rep = "/(int, int)"then
  yyy(p, org, k + 1, subseq(result, 1, i - 3)
   + Lit(value.s_(i - 2)/ value.s_(i - 1)), nextvar, map)
  else if fsig.rep = "=(int, int)"then
  yyy(p, org, k + 1, subseq(result, 1, i - 3)
   + if s_(i - 2) = s_(i - 1)then Littrue else Litfalse, nextvar, map)
  else if fsig.rep = ">(int, int)"then
  yyy(p, org, k + 1, subseq(result, 1, i - 3)
   + if value.s_(i - 2) > value.s_(i - 1)then Littrue else Litfalse, nextvar, map)
  else if fsig.rep = "∨(bits, bits)"then
  yyy(p, org, k + 1, subseq(result, 1, i - 3)
   + [ Lit.toint(bits.value.s_(i - 2) ∨ bits.value.s_(i - 1))], nextvar, map)
  else if fsig.rep = "∧(bits, bits)"then
  yyy(p, org, k + 1, subseq(result, 1, i - 3)
   + [ Lit.toint(bits.value.s_(i - 2) ∧ bits.value.s_(i - 1))], nextvar, map)
  else if fsig.rep = "<<(bits, int)"then
  yyy(p, org, k + 1, subseq(result, 1, i - 3)
   + [ Lit.toint(bits.value.s_(i - 2) << value.s_(i - 1))], nextvar, map)
  else if fsig.rep = ">>(bits, int)"then
  yyy(p, org, k + 1, subseq(result, 1, i - 3)
   + [ Lit.toint(bits.value.s_(i - 2) >> value.s_(i - 1))], nextvar, map)
  else if fsig.rep = "-(real, real)"then
  yyy(p, org, k + 1, subseq(result, 1, i - 3)
   + [ Reallit.representation(casttoreal.value.s_(i - 2) - casttoreal.value.s_(i - 1))], nextvar, map)
  else yyy(p, org, k + 1, result + rep, nextvar, map)

function inline(p:program, org:seq.symbol, k:int, result:seq.symbol, nextvar:int, nopara:int, code:seq.symbol, map:worddict.seq.symbol, options:seq.word)expandresult
 if length.code = 1 ∧ code = [ var.1] ∧ nopara = 1 then
 // function just returns result // yyy(p, org, k + 1, result, nextvar, map)
 else
  let len = length.result
  let t = backparse(result, len, nopara, empty:seq.int) + [ len + 1]
   assert length.t = nopara + 1 report"INLINE PARA PROBLEM"
   let new = if"STATE"_1 ∉ options ∧ issimple(p, nopara, code)then
   let pmap = simpleparamap(result, t, emptyworddict:worddict.seq.symbol, nopara)
     yyy(p, code, 1, empty:seq.symbol, nextvar, pmap)
   else expandinlineX(result, t, emptyworddict:worddict.seq.symbol, nopara, empty:seq.symbol, nextvar, code, p)
    yyy(p, org, k + 1, subseq(result, 1, t_1 - 1) + code.new, nextvar.new, map)

function simpleparamap(s:seq.symbol, t:seq.int, pmap:worddict.seq.symbol, i:int)worddict.seq.symbol
 if i = 0 then pmap
 else
  simpleparamap(s, t, add(pmap, toword.i, subseq(s, t_i, t_(i + 1) - 1)), i - 1)

function expandinlineX(s:seq.symbol, t:seq.int, pmap:worddict.seq.symbol, i:int, newcode:seq.symbol, nextvar:int, inlinecode:seq.symbol, p:program)expandresult
 // when i > 0 then assigning parameters to new local variables //
 if i = 0 then
 let r = yyy(p, inlinecode, 1, empty:seq.symbol, nextvar, pmap)
   expandresult(nextvar.r, newcode + code.r)
 else
  expandinlineX(s, t, add(pmap, toword.i, [ var.nextvar]), i - 1, subseq(s, t_i, t_(i + 1) - 1) + Define.toword.nextvar + newcode, nextvar + 1, inlinecode, p)




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



function simpleAcc(thunk:seq.symbol,resulttype:seq.word,lastvar:int,seqelement:symbol
,newmasteridx:symbol) breakresult
   let acc = Local(lastvar +1)
   let masteridx1 = Local(lastvar +2)
   let x2=  thunk @+( empty:seq.symbol,  
      if not.isabstractbuiltin.@e then @e
        else if  fsig.@e="@e"  then seqelement
        else if  fsig.@e="@i"  then masteridx1
        else if fsig.@e="@acc"  then acc
        else @e)
    breakresult([ Lit.1,Lit.lastvar,Loopblock("ptr," + resulttype + ", int,  int)")],
        x2+ [  newmasteridx, continue.3],
     [acc],
     lastvar+3,masteridx1)
 

 function    checkCompoundAcc(result:seq.word,s:symbol,i:int,noflds:int) seq.word
        if i > 4 * noflds then
        if s=Local.1 then  "fail" else result
       else if i mod 4 =0 then
         if isdefine.s then result+(fsig.s)_2 else "fail"
        else      
         if   s &in [ [Local.1],[Lit.(i / 4)],[symbol("IDX(T seq, int)","int builtin","int"),
         symbol("IDX(T seq, int)","real builtin","real"),
         symbol("IDX(T seq, int)","ptr builtin","ptr"),
         symbol("IDX(T seq, int)","boolean builtin","boolean")
         ]]_(i mod 4) then
          result  else "fail"
          
   
 function breakAccumalator(p:program,thunk:seq.symbol,resulttype:seq.word,lastvar:int,seqelement:symbol
,newmasteridx:symbol) breakresult
 //  lastvar+1 to lastvar+nopara.last.code are accumalators //
 //  lastvar+1+nopara.last.code lastvar+nopara.last.code+nopara.accfunc-1 are location of parameters for lastvar //
 let accfunc=last.thunk
let  ttt=lookupcode(p,last.thunk)
let code=removeoptions.code.ttt
let mylist=if isempty.code &or not.isrecord.last.code   then "" else
      let t=code @  checkCompoundAcc("", @e,@i,nopara.last.code)
      if "fail"_1 &in t then "" else t
 if isempty.mylist then simpleAcc(thunk,resulttype,lastvar,seqelement,newmasteridx )
 else 
 let masteridx=lastvar+length.mylist+1
 let x= mylist @ add(emptyworddict:worddict.seq.symbol ,   @e, [Local.( lastvar+@i)]) 
let pmap= paratypes.accfunc << 1 @ add(x , toword.(@i+1), [Local.( masteridx+@i)]) 
  let nextvar=   masteridx+nopara.accfunc 
   let r = yyy(p, subseq(code,4 * length.mylist+1,length.code-1), 1, empty:seq.symbol, nextvar, pmap)
    let thunkcode=    subseq(thunk,2,length.thunk-1)  @+( empty:seq.symbol,  
      if not.isabstractbuiltin.@e then @e
        else if  fsig.@e="@e"  then seqelement
        else if  fsig.@e="@i"  then Local.masteridx
        else  @e)+
        arithseq(nopara.accfunc-1,-1,nextvar-1) @+( empty:seq.symbol, 
         Define.toword(@e))+code.r + newmasteridx+continue.(length.mylist+2)    
    let orgacc=   nextvar.r
   let loopcode = arithseq(nopara.last.code,4,2) @+  ([Define.orgacc], [Local.orgacc]+ subseq(code,@e,@e+1))+
    [ Lit.1,Lit.lastvar,Loopblock("ptr," + subseq(fsig.last.code,3,length.fsig.last.code-1) + ", int,  int)")]
   let finalcode= arithseq(length.mylist,1,lastvar+1) @ +(empty:seq.symbol,(Local.@e))+last.code
    breakresult(loopcode,thunkcode,finalcode,orgacc+1,Local.masteridx)
 
type breakresult is record loopcode:seq.symbol,thunkcode:seq.symbol,finalcode:seq.symbol,nextvar:int,
     masteridx:symbol

function print(b:breakresult) seq.word
   "loopcode:"+print.loopcode.b
   +EOL+"thunkcode:"+print.thunkcode.b
  +EOL+"finalcode:"+print.finalcode.b
  +EOL+"nextvar:"+print.nextvar.b
   
   

function applycode4(p:program, org:seq.symbol, k:int, code:seq.symbol, nextvar:int, map:worddict.seq.symbol)expandresult
 let totallength = nextvar + 1
 let applysym = org_k
 let ds=(typerep.parameter.(paratypes.applysym)_1)_1
//   assert  code_-1 =Lit.0   report  print.code_-1+ ds  +print.org //
 let seqelementkind =if ds &in "int real" then ds else 
  if ds &in "bit byte" then "int"_1 else "ptr"_1
 let resulttype = [(module.applysym)_1]
  let idxp = Idx."ptr"_1
 let idxi = Idx."int"_1
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
// assert code_-1 =Lit.0 &or print.exitexp &in ["%1 @e()builtin.int =(int, int)builtin",
 "%1 @e()builtin.ptr =(myinternaltype, myinternaltype)symbol"
 ]
  report "thunk0"+print.thunk0 +EOL+"exitexp:"+print.exitexp //
  let checknoop = if length.thunk0 = 10 &and exitexp=[Lit.0] 
  ∧ thunk0 @ +("", dfg.@e)
  = "builtin @acc $define ? builtin @e $define ? % $int 0 $int 1 % $record RECORD seq +"then
     let b2 = backparse(code, t_1 - 1, 2, empty:seq.int)
     if subseq(code, b2_1, b2_2 - 1) = [ Constant2.Emptyseq]then subseq(code, 1, b2_1 - 1)
    else empty:seq.symbol
  else empty:seq.symbol
   if not.isempty.checknoop then yyy(p, org, k + 1, checknoop, nextvar, map)
   else
       let part1 = subseq(code, 1, t_1 - 1) + [ Lit.1, Idx."int"_1, Define.totallength]
     let codeparts= breakAccumalator(p ,thunk0,resulttype, value.theseq,seqelement,newmasteridx) 
     let masteridx=masteridx.codeparts
      let exitexp2=if exitexp=[Lit.0] then empty:seq.symbol else  exitexp @ +(empty:seq.symbol,
         if not.isabstractbuiltin.@e then @e
        else if  fsig.@e="@e"  then seqelement
        else if  fsig.@e="@i"  then masteridx
        else  @e) +[ Lit.2 ,Lit.3, Br, Local.totallength , Lit.1,PlusOp,Exit,newmasteridx,Exit,  Block(typeint,3)]
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
         theseq, Lit.0,idxi,Defineseqtype ,
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
   //    yyy(p, org, k + 1, part1 + kk, nextvar.codeparts, map)
   
   // zz &in "seq char mytype int token templatepart  myinternaltype UTF8 encoding llvmtype
    Lcode2 slotrecord mapele liblib parc attribute2 prettyresult internalbc"  //
    
        
         
   function  packedtype( ds:word) seq.symbol
     let multOp=symbol("*(int,int)","standard","int")
             let GEP=symbol("GEP(T seq, int)","ptr builtin","ptr")
        if ds &in "bit" then   
                [symbol("extractbit(T seq,int)","int builtin","T")]  
     else  if ds &in  "byte" then
               [symbol("extractbyte(T seq,int)","int builtin","T")]
      else  // element represented by multiple words //
         [    Lit.toint.ds,multOp, Lit.2, PlusOp ,GEP]
      


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
   if isnocall.sym2 &or sym2 ∈ pending then processed
   else
     let r = lookupcode(processed, sym)
      if isdefined.r then processed
     else
      let rep2 = lookupcode(knownsymbols, sym2)
       if length.code.rep2 > 0 then depthfirst(knownsymbols, alltypes, 1, pending + sym2, processed, code.rep2, sym2)else processed
   depthfirst(knownsymbols, alltypes, i + 1, pending, newprg, code, s)

________________________________

Function addoptions(code:seq.symbol, options:seq.word)seq.symbol
 if options = ""then code
 else
  let codewithoutoptions = if length.code > 0 ∧ last.code = Optionsym then subseq(code, 1, length.code - 2)
  else code
   codewithoutoptions + Words.options + Optionsym

Function caloptions(p:program, code:seq.symbol, nopara:int, modname:seq.word, fsig:seq.word)seq.word
  if fsig = "∈(int, int seq)"
  ∨ fsig = "∈(word, word seq)"
  ∨ fsig = "_(int seq, int)"
  ∨ fsig = "_(word seq, int)"then
  ""
  else
   let options = getoption.code
   let codeonly = if last.code = Optionsym then subseq(code, 1, length.code - 2)else code
   let newoptions = options
   + if"STATE"_1 ∉ options ∧ codeonly @ ∨(false, hasstate(p, @e))then"STATE"
   else""
    newoptions
    + if"NOINLINE"_1 ∈ options ∨ length.code > 20 ∨ checkself(fsig, modname, codeonly)then
    ""
    else"INLINE"


function checkself(fsig:seq.word, module:seq.word, s:seq.symbol)boolean s @ ∨(false, fsig = fsig.@e ∧ module = module.@e)



// statebit is set on option so that adding an option doesn't auto add a inline bit //

Function issimple(p:program, nopara:int, code:seq.symbol)boolean
 between(length.code, 1, 15) ∧ (nopara = 0 ∨ checksimple(p, code, 1, nopara, 0))


function checksimple(p:program, code:seq.symbol, i:int, nopara:int, last:int)boolean
 // check that the parameters occur in order and they all occur exactly once //
 // Any op that may involve state must occur after all parameters //
 if i > length.code then last = nopara
 else if nopara < last ∧ // should also check for loopblock // hasstate(p, code_i)then // state op between parameters // false
 else
  let rep = code_i
   if islocal.rep then
   let parano = value.rep
     if parano = last + 1 then checksimple(p, code, i + 1, nopara, last + 1)else false
   else checksimple(p, code, i + 1, nopara, last)

---------------------------

Function pass2(placehold:program, alltypes:typedict)program 
let bin=  toseq.toset.placehold @+(empty:seq.symbol,     
 let  d=lookupcode(placehold,@e)
   if  "BUILTIN"_1 &in getoption.code.d then [@e] else empty:seq.symbol )
toseq.toset.placehold @ depthfirst(program.asset.bin, placehold, alltypes, @e)

Function uses(p:program, roots:set.symbol)set.symbol uses(p, empty:set.symbol, roots)

 Function removeoptions(code:seq.symbol )seq.symbol
  if length.code > 0 ∧ last.code = Optionsym then subseq(code, 1, length.code - 2)
  else code

Function defines(p:program, roots:set.symbol)seq.symbol toseq.roots @ +(empty:seq.symbol, 
if isconstantorspecial.@e ∨   isabstract.modname.@e then empty:seq.symbol
 else [@e])
 


function uses(p:program, processed:set.symbol, toprocess:set.symbol)set.symbol
 if isempty.toprocess then processed
 else
  let q = asset(toseq.toprocess @ +(empty:seq.symbol, let d = code.lookupcode(p, @e)
  if isempty.d then constantcode.@e else d))
   uses(p, processed ∪ toprocess, q - processed)

