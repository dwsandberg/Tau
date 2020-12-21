
   
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

Function firstopt(p:program, rep:symbol, code:seq.symbol, alltypes:typedict)program
 let nopara = nopara.rep
  if isbuiltin.module.rep then
  let options = caloptions(p, code, nopara, module.rep, fsig.rep)
    map(p, symbol(fsig.rep, module.rep, returntype.rep), addoptions(code, options))
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

function yyy(p:program, org:seq.symbol, k:int, result:seq.symbol, nextvar:int, map:worddict.seq.symbol)expandresult
 if k > length.org then expandresult(nextvar, result)
 else
  let sym = org_k
  let len = length.result
   if isconst.sym then yyy(p, org, k + 1, result + sym, nextvar, map)
   else  if isspecial.sym then
   if(fsig.sym)_1 = "BLOCK"_1 ∧ fsig.sym = "BLOCK 3"then
    let t = backparse(result, len, 3, empty:seq.int) + [ len + 1]
     let condidx = t_2 - 4
     let cond = result_condidx
      if isbr.result_(condidx + 3) ∧ isconst.cond then
      let keepblock = if value.cond = 1 then value.result_(condidx + 1)else value.result_(condidx + 2)
       let new = subseq(result, t_keepblock, t_(keepblock + 1) - 2)
        yyy(p, org, k + 1, subseq(result, 1, condidx - 1) + new, nextvar, map)
      else yyy(p, org, k + 1, result + sym, nextvar, map)
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
    else if len > 2 ∧ isnotOp.result_(len - 2) ∧ fsig.sym = "BR 3"then
    yyy(p, org, k + 1, subseq(result, 1, len - 3) + [ result_len, result_(len - 1), Br], nextvar, map)
    else yyy(p, org, k + 1, result + sym, nextvar, map)
   else if(fsig.sym)_1 ∈ "apply3"then applycode4(p, org, k, result, nextvar, map)
   else
    let nopara = nopara.sym
    let dd = code.lookupcode(p, sym)
     if not.isempty.dd ∧ "INLINE"_1 ∈ options.dd then
     let code = if last.dd = Optionsym then subseq(dd, 1, length.dd - 2)else dd
       if isempty.code then yyy(p, org, k + 1, result + sym, nextvar, map)
       else inline(p, org, k, result, nextvar, nopara, code, map, options.dd)
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
        if isbuiltin.module.sym then opttwoopbuiltin(p, org, k, result, nextvar, map, sym)
        else if last.module.sym = "seq"_1
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
  let j = value.s_(i - 1)
   let x = s_(i - 2)
    if between(j, 0, length.constantcode.x - 1)then
    yyy(p, org, k + 1, subseq(result, 1, i - 3) + [(constantcode.x)_(j + 1)], nextvar, map)
    else yyy(p, org, k + 1, result + rep, nextvar, map)
  else if fsig.rep = "+(int, int)"then
  if isrecordconstant.s_(i - 2)then
   // address calculation // yyy(p, org, k + 1, result + rep, nextvar, map)
   else
    yyy(p, org, k + 1, subseq(result, 1, i - 3)
    + Lit(value.s_(i - 2) + value.s_(i - 1)), nextvar, map)
  else if fsig.rep = "*(int, int)"then
  yyy(p, org, k + 1, subseq(result, 1, i - 3)
   + Lit(value.s_(i - 2) * value.s_(i - 1)), nextvar, map)
  else if fsig.rep = "-(int, int)"then
  yyy(p, org, k + 1, subseq(result, 1, i - 3)
   + Lit(value.s_(i - 2) - value.s_(i - 1)), nextvar, map)
  else if fsig.rep = "/(int, int)" ∧ value.s_(i - 1) ≠ 0 then
  yyy(p, org, k + 1, subseq(result, 1, i - 3)
   + Lit(value.s_(i - 2) / value.s_(i - 1)), nextvar, map)
  else if fsig.rep = "=(int, int)"then
  yyy(p, org, k + 1, subseq(result, 1, i - 3)
   + if s_(i - 2) = s_(i - 1)then Lit.1 else Lit.0, nextvar, map)
  else if fsig.rep = ">(int, int)"then
  yyy(p, org, k + 1, subseq(result, 1, i - 3)
   + if value.s_(i - 2) > value.s_(i - 1)then Lit.1 else Lit.0, nextvar, map)
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

'function applycode3(p:program, org:seq.symbol, k:int, code:seq.symbol, nextvar:int, map:worddict.seq.symbol)expandresult
 // should do multiply once at start of seq instead of at access to every element. Replace will add of stride //
 let totallength = nextvar + 1
 let applysym = org_k
 let seqelementkind =(typerep.parameter.(paratypes.applysym)_1)_1
 let resulttype = [(module.applysym)_1]
 let STKRECORD = symbol("STKRECORD(ptr, ptr)","builtin","ptr")
 let nullptr = symbol("nullptr","builtin","ptr")
 let idxp = Idx."ptr"_1
 let idxi = Idx."int"_1
 let descleft = Lit.-2
 let theseq = Local(nextvar + 2)
 let acc = Local(nextvar + 3)
 let masteridx = Local(nextvar + 4)
 let idx = Local(nextvar + 5)
 let lastidx = Local(nextvar + 6)
 let stk = Local(nextvar + 7)
 let seqtype= Local(nextvar + 8)
 let newidx = Local(nextvar + 9)
 let Definenewidx = Define(nextvar + 9)
 let Definenewmasteridx = Define(nextvar + 10)
 let newmasteridx = Local(nextvar + 10)
 let Defineseqelement = Define(nextvar + 11)
 let seqelement = Local(nextvar + 11)
 let pseq = Fref.symbol("_(int pseq,int)", "int seq","int")
 let typesize=value.code_(-1)
 // let pl=paratypes.applysym
  let x=  [toword.typesize]+seqelementkind+resulttype 
    assert  x in [
    " 1 int int" ,"4 ptr ptr" ,"4 ptr int","5 ptr ptr","1 ptr ptr", "1 ptr int",
    " 1 int real"," 1 int ptr    ",  "3 ptr int","3 ptr ptr","5 ptr int"
  ,"  2 ptr ptr   "
  ]  
  report  "x"+x  //
 let sym = code_(-2)
 let t = backparse(code, length.code - 2, nopara.code_(length.code - 1), empty:seq.int)
 let thunk0 = subseq(code,t_1,length.code-1) 
   assert fsig.thunk0_1 = "@acc"report"apply error" + t @ +("", toword.@e)
  + code @ +(" &br code:", print.@e)
  + thunk0 @ +(" &br code:", print.@e)
  + " &br nopara"
  + toword.nopara.code_(length.code - 1)
  + " &br"
  + t @ +("", toword.@e)
  let checknoop = if length.thunk0 = 10
  ∧ thunk0 @ +("", dfg.@e)
  = "builtin @acc $define ? builtin @e $define ? % $int 0 $int 1 % $record RECORD seq +"then
  let b2 = backparse(code, t_1 - 1, 2, empty:seq.int)
    if subseq(code, b2_1, b2_2 - 1) = [ Constant2.Emptyseq]then
    subseq(code, 1, b2_1 - 1)
    else empty:seq.symbol
  else empty:seq.symbol
   if not.isempty.checknoop then yyy(p, org, k + 1, checknoop, nextvar, map)
   else
    let zz0=parameter.(paratypes.applysym)_3
    let zz=abstracttype.zz0
     let change = seqelementkind ∈ "real"  
     //  &or 
    zz &nin "encodingpair   word    symbol  myinternaltype block firstpass"
      &or ( zz in "encodingpair" &and print.parameter.zz0 in 
    ["symboltext","typename","llvmtypeele","symbolconstant","const3","stat5","llvmconst","match5"]) 
    assert change &or  not(zz in "encodingpair") &or  print.parameter.zz0 in ["seq.char"
  ,"word3"] 
     report "XJK"+print.zz0   //
   let fiveor9=if change then Lit.5 else Lit.9
    let part1 = subseq(code, 1, t_1 - 1) + [ Lit.1, Idx."int"_1, Define.totallength]
    let b = subthunk2(thunk0, 1, [ seqelement, masteridx], empty:seq.symbol)
    let thunk = [ acc] + (b << 1)
    let kk = [ Lit.1, Lit.0, descleft, nullptr, Lit.0,Lit(nextvar + 2), // the left side of the pseq remains to be processed when it is on the stack loop(seq, ptr, masteridx, idx, lastidx, stk)//
    // 1 // Loopblock("ptr," + resulttype + ", int, int, int, ptr,int, int)"), 
    // 2 if not(lastidx < idx){ idx < = lastidx then // lastidx, idx, GtOp, Lit.9
    , Lit.3, Br, 
    // 3 if not(masteridx > totallength )then exit // masteridx,Local.totallength,  GtOp, Lit.4, fiveor9, Br, 
    // 4 // acc, Exit
    , // 5 if descleft then // lastidx, descleft, EqOp, Lit.7, Lit.6, Br, 
    // 6 pop pseq continue(  b.top(stk),acc, masteridx,idx,descleft,pop(stk),seqtype // 
      stk, Lit.1, idxp, Lit.3 , idxp, acc, masteridx, idx, descleft, stk, Lit.0, idxi, seqtype, continue.7, 
    // 7 else descleft if not.ispseq.theseq then // 
    theseq, Lit.0, idxi, pseq, EqOp, Lit.10, Lit.8, Br, 
    // 8 start new seq ; continue( theseq,acc, masteridx, Lit.0, length.theseq, stk)// 
    theseq, acc, masteridx, Lit.0, theseq, Lit.1, idxi, stk,    
            theseq, Lit.0, idxi, 
     continue.7, 
    // 9 else--body--let newidx = idx + +, let newmasteridx = masteridx + +, let sequenceele = seq_(idx)continue(thunk, masteridx, idx, lastidx, seq, stk)//
    idx, Lit.1, PlusOp, Definenewidx
    , masteridx, Lit.1, PlusOp, Definenewmasteridx]
    +subblock(theseq,idx,seqtype,newidx, seqelementkind,typesize ,change )  
        +[Defineseqelement, theseq]
    + thunk
    + [ //, acc, seqelement, PlusOp, // newmasteridx, newidx, lastidx, stk, 
    seqtype, continue.7,
    // 10 descleft  continue( a.theseq,    acc,      masteridx, newidx,  descleft,  push(stk,theseq) ,Lit.0 ) //
        theseq, Lit.2, idxp, acc,masteridx, newidx,  descleft,  stk ,theseq,STKRECORD
        ,Lit.0, continue.7,
   Block(mytype.resulttype, 10)]
   //  assert subseq(x,1,3) = "1 int ptr" report  (part1 + kk) @@ +(" &br result", print.@e)
   //   yyy(p, org, k + 1, part1 + kk, nextvar + 12, map)
   
   // zz &in "seq char mytype int token templatepart  myinternaltype UTF8 encoding llvmtype
    Lcode2 slotrecord mapele liblib parc attribute2 prettyresult internalbc"  //
    

/function  subblock(theseq:symbol,idx:symbol,
seqtype:symbol,newidx:symbol, seqelementkind:word ,typesize:int
,change:boolean ) seq.symbol  
     let threeor2=if change then Lit.3 else Lit.2
   if typesize > 1  then
  [ seqtype ,Lit.1000, GtOp, Lit.2, threeor2,Br,
           theseq, newidx, Callidx.seqelementkind,Exit,
           // 3 else if  not(seq > 1 )   then  Idx(theseq,idx) //
                  seqtype,Lit.1,  GtOp, Lit.5,Lit.4,Br,
                 theseq,newidx,Lit.1,PlusOp,Idx.seqelementkind,Exit,
            // else //  
            theseq
                 ,idx, seqtype, symbol("*(int,int)","builtin","int")
                 ,Lit.2
             ,PlusOp
           , Lit.0,symbol("cast(T seq, int, int)","builtin","ptr"),Exit,
        Block(mytype.[seqelementkind],5)]
    else 
   [ seqtype ,Lit.1000, GtOp, Lit.2, threeor2,Br,
           theseq, newidx, Callidx.seqelementkind,Exit,
           theseq,newidx,Lit.1,PlusOp,Idx.seqelementkind,Exit,
        Block(mytype.[seqelementkind],3)]  '

function subthunk2(s:seq.symbol, i:int, with:seq.symbol, found:seq.symbol)seq.symbol
 if i > length.s then found + s
 else if abstracttype.modname.s_i ≠ "builtin"_1 then subthunk2(s, i + 1, with, found)
 else
  let t = findindex((fsig.s_i)_1,"@e @i @exit")
  let news = if t > 3 then s else replace(s, i, with_t)
   subthunk2(news, i + 1, with, if t ∈ [ 3] ∧ isempty.found then found + s_i else found)

function applycode4(p:program, org:seq.symbol, k:int, code:seq.symbol, nextvar:int, map:worddict.seq.symbol)expandresult
 // should do multiply once at start of seq instead of at access to every element. Replace will add of stride //
 let totallength = nextvar + 1
 let applysym = org_k
 let seqelementkind =(typerep.parameter.(paratypes.applysym)_1)_1
 let resulttype = [(module.applysym)_1]
 let STKRECORD = symbol("STKRECORD(ptr, ptr)","builtin","ptr")
 let nullptr = symbol("nullptr","builtin","ptr")
 let idxp = Idx."ptr"_1
 let idxi = Idx."int"_1
 let descleft = Lit.-2
 let theseq = Local(nextvar + 2)
 let acc = Local(nextvar + 3)
 let masteridx = Local(nextvar + 4)
 let Definenewmasteridx = Define(nextvar + 10)
 let newmasteridx = Local(nextvar + 10)
 let Defineseqelement = Define(nextvar + 11)
 let seqelement = Local(nextvar + 11)
  let sym = code_(-2)
 let t = backparse(code, length.code - 2, nopara.code_(length.code - 1), empty:seq.int)
 let thunk0 = subseq(code,t_1,length.code-1) 
  assert fsig.thunk0_1 = "@acc"report"apply error" + t @ +("", toword.@e)
  + code @ +(" &br code:", print.@e)
  + thunk0 @ +(" &br code:", print.@e)
  + " &br nopara"
  + toword.nopara.code_(length.code - 1)
  + " &br"
  + t @ +("", toword.@e)
  let checknoop = if length.thunk0 = 10
  ∧ thunk0 @ +("", dfg.@e)
  = "builtin @acc $define ? builtin @e $define ? % $int 0 $int 1 % $record RECORD seq +"then
  let b2 = backparse(code, t_1 - 1, 2, empty:seq.int)
    if subseq(code, b2_1, b2_2 - 1) = [ Constant2.Emptyseq]then
    subseq(code, 1, b2_1 - 1)
    else empty:seq.symbol
  else empty:seq.symbol
   if not.isempty.checknoop then yyy(p, org, k + 1, checknoop, nextvar, map)
   else
    let zz0=parameter.(paratypes.applysym)_3
    let zz=abstracttype.zz0
       let part1 = subseq(code, 1, t_1 - 1) + [ Lit.1, Idx."int"_1, Define.totallength]
    let b = subthunk2(thunk0, 1, [ seqelement, masteridx], empty:seq.symbol)
    let thunk = [ acc] + (b << 1)
    let kk = [ Lit.1,Lit(nextvar + 2), 
    //  loop(seq, acc, masteridx)//
    // 1 // Loopblock("ptr," + resulttype + ", int,  int)"), 
    // 2  if  masteridx > totallength  then exit // 
        masteridx,Local.totallength,  GtOp, Lit.3, Lit.4, Br, 
    // 3 // acc, Exit,
      // 4 else  let newmasteridx = masteridx + 1, 
    let sequenceele = seq_(idx)
     continue(thseqeq,thunk,newmasteridx) //
         masteridx, Lit.1, PlusOp, Definenewmasteridx,
          theseq, Lit.0,idxi, Lit.0, EqOp ,Lit.2,Lit.3, Br,
         theseq, newmasteridx, Idx.seqelementkind, Exit, 
          theseq, masteridx, Callidx.seqelementkind ,   Exit,
         Block(mytype.[seqelementkind],3),   Defineseqelement, theseq]
    + thunk
+ [  newmasteridx, continue.3,   Block(mytype.resulttype, 4)]
   //  assert subseq(x,1,3) = "1 int ptr" report  (part1 + kk) @@ +(" &br result", print.@e)
   //   yyy(p, org, k + 1, part1 + kk, nextvar + 12, map)
   
   // zz &in "seq char mytype int token templatepart  myinternaltype UTF8 encoding llvmtype
    Lcode2 slotrecord mapele liblib parc attribute2 prettyresult internalbc"  //
    


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
  let newprg =
  let sym2 = basesym.sym
   if isnocall.sym2 then processed
   else if sym2 ∈ pending then processed
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
 let options = options.code
  if length.code = 0 then if not.isbuiltin.modname then"STATE"else""
  else if fsig = "in(int, int seq)" ∨ fsig = "in(word, word seq)"
  ∨ fsig = "∈(int, int seq)"
  ∨ fsig = "∈(word, word seq)"
  ∨ fsig = "_(int seq, int)"
  ∨ fsig = "_(word seq, int)"then
  ""
  else
   let codeonly = if last.code = Optionsym then subseq(code, 1, length.code - 2)else code
   let newoptions = options
   + if"STATE"_1 ∉ options ∧ codeonly @ ∨(false, hasstate(p, @e))then"STATE"
   else""
    newoptions
    + if"NOINLINE"_1 ∈ options ∨ length.code > 20 ∨ checkself(fsig, modname, codeonly)then
    ""
    else"INLINE"

function checkself(fsig:seq.word, module:seq.word, s:symbol)boolean fsig = fsig.s ∧ module = module.s

function checkself(fsig:seq.word, module:seq.word, s:seq.symbol)boolean s @ ∨(false, checkself(fsig, module, @e))


function isnotOp(s:symbol)boolean fsig.s = "not(boolean)" ∧ isbuiltin.module.s


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
   let parano = toint.(fsig.rep)_1
     if parano = last + 1 then checksimple(p, code, i + 1, nopara, last + 1)else false
   else checksimple(p, code, i + 1, nopara, last)

---------------------------

Function pass2(placehold:program, alltypes:typedict)program toseq.toset.placehold @ depthfirst(emptyprogram, placehold, alltypes, @e)

Function uses(p:program, roots:set.symbol)set.symbol uses(p, empty:set.symbol, roots)

Function defines(p:program, roots:set.symbol)seq.symbol toseq.roots @ +(empty:seq.symbol, defines2(p, @e))

function uses(p:program, s:symbol)seq.symbol
 let d = code.lookupcode(p, s)
  if isempty.d then constantcode.s else d

function uses(p:program, processed:set.symbol, toprocess:set.symbol)set.symbol
 if isempty.toprocess then processed
 else
  let q = asset(toseq.toprocess @ +(empty:seq.symbol, uses(p, @e)))
   uses(p, processed ∪ toprocess, q - processed)

function defines2(p:program, s:symbol)seq.symbol
 if isconstantorspecial.s ∨ isbuiltin.module.s ∨ isabstract.modname.s then empty:seq.symbol
 else
  let d = code.lookupcode(p, s)
   if isempty.d then empty:seq.symbol else [ s]