
Module pass2new

run mylib testnew

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

use mangle

use otherseq.mytype

use packedseq.seq.mytype

use seq.seq.mytype

use seq.mytype

use real

use intdict.sig

use ipair.sig

use blockseq.seq.sig

use intdict.seq.sig

use ipair.seq.sig

use seq.seq.seq.sig

use seq.seq.sig

use stack.seq.sig

use seq.sig

use set.sig

use encoding.fsignrep

use seq.encodingrep.fsignrep

use intdict.fsignrep

use seq.fsignrep

use stacktrace

use stdlib

use symbol

use otherseq.word

use seq.seq.word

use seq.word

use set.word

use deepcopy.intercode

use seq.symbol

use set.symbol

use seq.firstpass

use libdesc

use processOptions

Function pass2new(knownsymbols:symbolset, mods:seq.firstpass, compiled:symbolset)intercode
 let roots=getroots(mods) 
  let roots2=@(+,mangledname,"",toseq.roots)
 // let p1=if length.compiled2 > 0 then bbbfirst(knownsymbols, compiled2, "all", emptyprg,mytype."?")
 else emptyprg //
 let b = bbbfirst(knownsymbols, roots2, "all", emptyprg,mytype."?")
  // assert false report"dumpprg"+ dumpprg.b //
  let sigreps=getfsignrep.b
  let ic =   intercode( sigreps ,defines(compiled,sigreps,1,empty:seq.int))
     let libmods=libdesc(b,ic, mods , knownsymbols)
    addlibmods(libmods,ic) 
    
    
 /function   toexport(p:prg,processed:set.sig, toprocess:set.sig) set.sig
   if isempty.toprocess then processed else 
    let p= toseq.asset.@(+,exportcode,empty:seq.sig,     toseq.toprocess)
      toexport(fs,processed &cup toprocess, p-processed)

      


function defines(compiled:symbolset,ss:seq.fsignrep,i:int,result:seq.int) seq.int
if i > length.ss then result else let s=ss_i
if (length.module.s=1 &and (module.s)_1 in "$  local $fref $constant $words $word $int" ) &or length.code.s=0 
 &or isdefined.lookupsymbol(compiled, mangledname.s) then
   defines(compiled,ss,i+1,result)
else  defines(compiled,ss,i+1,result+i)
     


  
type backresult is record code:seq.sig, places:seq.int

Function firstopt(p:prg, c:seq.seq.word, code:seq.sig)prg
 let nopara = length.c - 2
 let pdict=addpara(empty:intdict.seq.sig, nopara)
 let code2 = value.yyy(p, code, 1, nopara + 1, pdict)
 let s = sig(c_1, @(+, mytype, empty:seq.mytype, subseq(c, 3, length.c)), mytype.c_2, code2,mytype."?")
  // assert length.code < 10 report"UUU"+ print.code +"
&p"+ print.code2 //
  let a = handletail(code2, s,c_1)
    // assert not(t_1 in"testoptZtestopt")report"PROCESSProC"+ toword.length.code2 + print.code //
   let a2=value.yyy(p,a,1,nopara+1,pdict)
   add(p, s, a2)

function breaklines2(a:seq.int, i:int, last:int, result:seq.seq.int)seq.seq.int
 if i > length.a then result
 else if false then
 breaklines2(a, i + 1, last, result )
 else breaklines2(a, i + 1, last, result)
 
function handletail(code:seq.sig, self:sig,xx:seq.word)seq.sig
 if length.code < 4 then code
 else if isblock.last.code then
 let i = length.code
  let blksize = lownopara.code_i
   assert blksize ≥ 0 report"BAK 6"
   let args = backparseblock(code, i - 1, blksize, empty:seq.seq.int)
   let blks = subseq(places.args, 2, length.places.args) + [ i]
    if isloopblock.code_(blks_1 - 1)then code.args
    else
     let b = @(+, findtail(code.args, self), empty:seq.seq.int, blks)
      if length.b = 0 then code.args
      else
       // assert length.code &ne 184 report"PROCESSProC"+ print.code.args //
       let nopara = nopara.decode.self
       let plist = @(+, var, empty:seq.sig, arithseq(nopara, 1, 1))
       let continue = [ continue.nopara]
        // let code1 = @(+, adjustvar(nopara), empty:seq.sig, code.args)//
        let code1 = adjustvar(code.args, nopara, 1, empty:seq.sig)
        let code2 = @(adjustbr.1, identity, code1, blks)
        let code3 = @(addcontinue.continue, identity, code2, reverse.b)
        //  assert  not(xx="breaklines") report "DFG"+toword.length.b+"K"+print.code3 //
        let entry = plist + lit(nopara + 1) + loopblock(nopara + 1)
        let code4 = entry + subseq(code3, 1, length.code3 - 1) + block(length.blks + 1)
          code4
 else code.backparse2(code, length.code, 1, empty:seq.int)

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

function addcontinue(continue:seq.sig, code:seq.sig, l:seq.int)seq.sig
 let a = subseq(code, 1, l_1 - 1) + continue + subseq(code, l_2 + 1, length.code)
  a

function adjustbr(delta:int, code:seq.sig, i:int)seq.sig
 if code_(i - 1) = br then
   let b = adjustlit(code, delta, 0, i - 2)
   let a = adjustlit(code, delta, 0, i - 3)
   subseq(code, 1, i - 4) + [ a, b] + subseq(code, i - 1, length.code)
 else code

function findtail(s:seq.sig, self:sig, i:int)seq.seq.int
  if s_(i-1)=exit then
   let j=skipskip(s,i-2)
   if  s_(j) = self then [[j,i-1]] else  empty:seq.seq.int  
else   empty:seq.seq.int
 
 function  skipskip(s:seq.sig,i:int) int
     if s_i=skip then skipskip(s, i-1) else  i 

function print(s:seq.int)seq.word @(+, toword,"", s)

function adjust(code:seq.sig, blks:seq.seq.int, no:int, delta:int, after:int, blkinsert:boolean)backresult
 if no > length.blks then
 // assert @(seperator("/"), print,"", blks)="1 11 16 17 18 / 0 20 27 / 0 29 36"report"JK"+ @(seperator("/"), print,"", blks)//
  let index = last.last.blks
  let t = @(+, second, empty:seq.int, blks)
   // assert false report print(subseq(code, index - 2, index + 2))//
   // assert print([ code_index])in ["BLOCK 3"]report"JK"+ print([ code_index])+ @(seperator("/"), print,"", blks)//
   let newcode = if isblock.code_index then
   subseq(code, 1, index - 1) + block.length.blks + subseq(code, index + 1, length.code)
   else code
    // assert length.blks < 2 report"
&br"+ @(seperator("/"), print,"", blks)+"
&br"+ toword.length.code + print.newcode +"
&br"+ print.[ code_last.last.blks]//
    backresult(newcode, t)
 else
  // assert @(seperator("/"), print,"", blks)="1 11 16 17 18 / 0 20 27 / 0 29 36"report"JKP"+ @(seperator("/"), print,"", blks)//
  let blk = blks_no
  let kind = blk_1
   assert kind in [ 0, 1, 2]report"TTT" + toword.kind
    if kind = 1 ∧ delta > 0 then
    // adjust br labels //
     let a = adjustlit(code, delta, after, blk_3)
     let b = adjustlit(code, delta, after, blk_4)
     let newcode = subseq(code, 1, blk_3 - 1) + [ a, b]
     + subseq(code, blk_4 + 1, length.code)
      // assert [ code_(blk_3), code_(blk_4)]= [ a, b]report"JKL"+ print.code +"
&br"+ print.newcode //
      adjust(newcode, blks, no + 1, delta, after, blkinsert)
    else if kind = 2 ∧ blkinsert then
    // block - - insert args in blks //
     let addedblks = cvtblock(code, blk, 3, empty:seq.seq.int)
      // assert false report print.blk //
      let index = last.blk
      let a = adjust(code, blks, 1, length.addedblks - 1, no, false)
      let b = adjust(code.a, addedblks, 1, no - 1, 0, false)
      let newblks = subseq(blks, 1, no - 1) + addedblks + subseq(blks, no + 1, length.blks)
       adjust(code.b, newblks, no + length.addedblks, 0, 0, blkinsert)
    else adjust(code, blks, no + 1, delta, after, blkinsert)

function adjustlit(code:seq.sig, delta:int, after:int, index:int)sig
 let val = value.code_index
  if val > after then lit(delta + val)else code_index

function cvtblock(code:seq.sig, blks:seq.int, no:int, result:seq.seq.int)seq.seq.int
 if no > length.blks then result
 else
  let i = blks_no
  let kind = code_(i - 1)
  let new = if kind = br then [ 1, blks_(no - 1), i - 3, i - 2]
  else // assert kind in [ exit, block]report"check 5"// [ 0, blks_(no - 1), i]
   cvtblock(code, blks, no + 1, result + new)

function backparse2(s:seq.sig, i:int, no:int, result:seq.int)backresult
 // this will merge blocks //
 if no = 0 then backresult(s, result)
 else
  assert i > 0 report"B" + print.s
  let nopara = nopara.s_i
   if isblock.s_i then
   let args = backparseblock(s, i - 1, nopara, empty:seq.seq.int)
    let t = includedefine2(code.args,(places.args)_1)
     backparse2(value.t, index.t - 1, no - 1, [ index.t] + result)
   else if nopara = 0 then
   let t = includedefine2(s, i)
     backparse2(value.t, index.t - 1, no - 1, [ index.t] + result)
   else
    let args = backparse2(s, i - 1, nopara, empty:seq.int)
    let t = includedefine2(code.args,(places.args)_1)
     backparse2(value.t, index.t - 1, no - 1, [ index.t] + result)

function includedefine2(s:seq.sig, first:int)ipair.seq.sig
 if first = 1 then ipair(1, s)
 else if isdefine.s_(first - 1)then
 let t = backparse2(s, first - 2, 1, empty:seq.int)
   includedefine2(code.t,(places.t)_1)
 else ipair(first, s)

function backparseblock(s:seq.sig, i:int, no:int, result:seq.seq.int)backresult
 // assert length.s < 17 &or [ i, no]in [ [ 60, 30]]report"KL"+ toword.i +"no:"+ toword.no + @(seperator."/", print,"", result)+"
&br"+ print.subseq(s, 1, i)//
 if no = 0 then adjust(s, result, 1, 0, 0, true)
 else if s_i = br then
 let t = backparse2(s, i - 1, 3, empty:seq.int)
  let args = [ 1] + places.t
   backparseblock(code.t, args_2 - 1, no - 1, [ args + (i + 1)] + result)
 else if s_i = exit ∧ isblock.s_(i - 1)then
 let t = backparseblock(s, i - 2, nopara.s_(i - 1), empty:seq.seq.int)
   if s_((places.t)_2 - 1) = br then
   let newcode = subseq(code.t, 1, i - 3) + skip + skip
    + subseq(code.t, i, length.code.t)
     // assert false report"JK"+ print.subseq(code.t, 1, i + 1)+"
&br"+ print.subseq(newcode, 1, i + 1)+"
&br"+ toword.i + print.places.t //
     let args = [ 2] + places.t
      backparseblock(newcode, args_2 - 1, no - 1, [ args + (i + 1)] + result)
   else
    // is loop - - cannot merge blocks //
    let args = [ 0] + places.t
     backparseblock(code.t, args_2 - 1, no - 1, [ args + (i + 1)] + result)
 else
  assert s_i = exit ∨ (fsig.decode.s_i)_1 in "CONTINUE LOOPBLOCK"report"BAK 4" + toword.no + print.subseq(s, 1, i) 
  + " &br <<<"
  + print.subseq(s, i + 1, length.s)
  + " &br"
  + @(seperator."/", print,"", result)
  let t = backparse2(s, i - 1, nopara.s_i, empty:seq.int)
  let args = [ 0] + places.t
   backparseblock(code.t, args_2 - 1, no - 1, [ args + (i + 1)] + result)

function second(s:seq.int)int s_2

function var(i:int)sig var.toword.i

function var(w:word)sig  sig([ w], empty:seq.mytype, mytype."local",empty:seq.sig,mytype."?")


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
else  
if not.lookcloser.s_i then yyy(p, s, i + 1, nextvar, map) else
   let rep=decode.s_i
  if isdefine.s_i then
   if i > 1 ∧ (isconst.s_(i - 1) ∨ islocal.s_(i - 1))then
   yyy(p, replace(s, i - 1, 2, empty:seq.sig), i - 1, nextvar, replace(map, valueofencoding.(code.rep)_1, [ s_(i - 1)]))
   else
    yyy(p, replace(s, i, 1, [ define.toword.nextvar]), i + 1, nextvar + 1, replace(map, valueofencoding.(code.rep)_1, [ var.nextvar]))
 else 
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
  else if isloopblock.s_i then
 let nopara = nopara.s_i - 1
  let firstvar = value.s_(i - 1)
   yyy(p, replace(s, i - 1, 1, [ lit.nextvar]), i + 1, nextvar + nopara, addlooplocals(map, firstvar, nextvar, nopara, 0))
 else if isrecord.s_i ∧ i > 2 then
 let nopara = nopara.s_i
  let args = subseq(s, i - nopara, i - 1)
   if @(∧, isconst, true, args) ∧ length.args = nopara then
     yyy(p, replace(s, i - nopara, nopara + 1, [ constant.args]), i - nopara, nextvar, map)
   else yyy(p, s, i + 1, nextvar, map)
 else if s_i = IDXUC ∧ i > 2 ∧ isconst.s_(i - 1)then
 if isconst.s_(i - 2)then
  let j = value.s_(i - 1)
   let x = decode.s_(i - 2)
    if between(j, 0, length.code.x - 1)then
    yyy(p, replace(s, i - 2, 3, [(code.x)_(j + 1)]), i - 1, nextvar, map)
    else yyy(p, s, i + 1, nextvar, map)
  else yyy(p, s, i + 1, nextvar, map)
 else if isapply.s_i then
 let t = applycode(p, nextvar, s, i)
   yyy(p, code.t, index.t, nextvar.t, map)
 else if fsig.rep = "makereal(word seq)" ∧ isconst.s_(i - 1)then
 let arg1 = decode.s_(i - 1)
   if module.arg1 = "$words"then
   let  x=lit.representation.makereal.fsig.arg1 
     yyy(p, replace(s, i - 1, 2, [ x]), i, nextvar, map)
   else yyy(p, s, i + 1, nextvar, map)
 else if fsig.rep = "merge(word seq)" ∧ isconst.s_(i - 1)then
 let arg1 = decode.s_(i - 1)
   if module.arg1 = "$words"then
     yyy(p, replace(s, i - 1, 2, [ wordsig.merge.fsig.arg1 ]), i, nextvar, map)
   else yyy(p, s, i + 1, nextvar, map)
 else if fsig.rep = "decode(T erecord, T encoding)" ∧ s_(i - 2) = wordEncodingOp ∧ isconst.s_(i - 1)then
  let arg1 = decode.s_(i - 1)
   if module.arg1 = "$word"then
   let a1 = @(+, lit, empty:seq.sig, tointseq.decodeword.(fsig.arg1)_1)
    let d = [ lit.0, lit.length.a1] + a1 + RECORD(length.a1 + 2)
    let k = replace(s, i - 2, 3, d)
     yyy(p, replace(s, i - 2, 3, d), i + length.d - 3, nextvar, map)
   else yyy(p, s, i + 1, nextvar, map)
 else if i > 2 ∧ (not.isconst.s_(i - 1) ∨ not.isconst.s_(i - 2))then
   yyy(p, s, i + 1, nextvar, map)
 else     if module.rep="builtin" then
  if s_i = plusOp then
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
   let new=replace(s, i - 2, 3, [ if value.s_(i - 2) = value.s_(i - 1)  then lit.1 else lit.0])
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
 else 
 if  fsig.rep="_(T seq, int)"  then
  let idx = value.s_(i - 1)
  let arg1 = decode.s_(i - 2)
  let words = name.arg1
   if module.arg1 = "$words" &and  between(idx, 1, length.words) then
      yyy(p, replace(s, i - 2, 3, [ wordsig.words_idx]), i - 1, nextvar, map)
   else if    module.arg1 = "$constant" &and  between(idx, 1, length.code.arg1-2) then
      yyy(p, replace(s, i - 2, 3, [ (code.arg1)_(idx+2)]), i - 1, nextvar, map)
   else yyy(p, s, i + 1, nextvar, map)
 else   if  fsig.rep="+(T seq, T seq)" &and module.rep="word seq" then
 let arg1 = decode.s_(i - 2)
  let arg2 = decode.s_(i - 1)
   if module.arg1 = "$words" ∧ module.arg2 = "$words"then
     yyy(p, replace(s, i - 2, 3, [ wordssig(name.arg1 + name.arg2)]), i - 1, nextvar, map)
   else yyy(p, s, i + 1, nextvar, map)
 else yyy(p, s, i + 1, nextvar, map)

function inline(p:prg, s:seq.sig, i:int, nextvar:int)expandresult
 let k = lookuprep(p, s_i)
  assert not((print.[ s_i])_1 = "message"_1)report print.[ s_i] + if issimple.k then"SIMPLE"else""
  let nopara = nopara.k
   if length.code.k = 1 ∧ code.k = [ var.1]then
   // function just returns result // expandresult(nextvar, i, replace(s, i, 1, empty:seq.sig))
   else
    let t = backparse(s, i - 1, nopara, empty:seq.int) + i
     assert length.t = nopara + 1 report"INLINE" + print.subseq(s, 1, i)
     let new = if issimple.k then expandsimpleinline(s, t, empty:intdict.seq.sig, nopara, nextvar, code.k, p)
     else expandinline(s, t, empty:intdict.seq.sig, nopara, empty:seq.sig, nextvar, code.k, p)
      expandresult(nextvar + nopara, t_1 + length.new, replace(s, t_1, i - t_1 + 1, new))

function expandsimpleinline(s:seq.sig, t:seq.int, pmap:intdict.seq.sig, i:int, nextvar:int, inlinecode:seq.sig, p:prg)seq.sig
 // when i > 0 then building paramenter map //
 if i = 0 then value.yyy(p, inlinecode, 1, nextvar, pmap)
 else
  expandsimpleinline(s, t, add(pmap, valueofencoding.var.i, subseq(s, t_i, t_(i + 1) - 1)), i - 1, nextvar, inlinecode, p)

function expandinline(s:seq.sig, t:seq.int, pmap:intdict.seq.sig, i:int, newcode:seq.sig, nextvar:int, inlinecode:seq.sig, p:prg)seq.sig
 // when i > 0 then assigning parameters to new local variables //
 if i = 0 then value.yyy(p, inlinecode, 1, nextvar, pmap)
 else
  expandinline(s, t, add(pmap, valueofencoding.var.i, [ var.nextvar]), i - 1, subseq(s, t_i, t_(i + 1) - 1) + define.toword.nextvar, nextvar + 1, inlinecode, p)

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
 let term1 = code.decode.code_(index - 2)
 let term2 = code.decode.code_(index - 3)
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
 ∧ code_(t_1) = emptyseqOp
 ∧ fsig.decode.term1_1 = "+(T seq, T)"
 ∧ last.module.decode.term1_1 = "seq"_1
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
  checknoop.code.decode.s_1

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



type rtype is record processed:prg, texts:seq.seq.word


use deepcopy.seq.word

function bbbfirst(knowsymbols:symbolset, s:seq.word,   pending:seq.word, processed:prg,rettyp:mytype)prg
if length.s=0 &or last.s = "EXTERNAL"_1 then
 assert length.s=0 &or s in ["EXTERNAL", [ last.pending] + "STATE EXTERNAL"]report"EXT" + s
  let c = codedown.last.pending
  let discard = sig(c_1, @(+, mytype, empty:seq.mytype, subseq(c, 3, length.c)), mytype.c_2, empty:seq.sig,rettyp)
   processed
else
bbb(knowsymbols, deepcopy.removeflags(s,length.s), 1, pending  , processed, empty:seq.sig)

function removeflags(s:seq.word,i:int) seq.word
if s_i in " PROFILE  builtinZinternal1Zinternal1 
builtinZinternal1Zwordzseq NOINLINE STATEZinternal1Zinternal1"then
   removeflags(s,i-1)
   else 
   // assert isempty.(asset.subseq(s,i+1,length.s)-asset."NOINLINE builtinZinternal1Zwordzseq
    builtinZinternal1Zinternal1 STATEZinternal1Zinternal1 PROFILE") report "XXX"+subseq(s,i+1,length.s) //
   subseq(s,1,i)

use seq.cached


 
   
 type cached is record      key:seq.word,s:sig
 
 type  ecached is encoding cached
 
 function assignencoding(l:int, s:cached)int assignrandom(l,s)
 
 function =(a:cached,b:cached) boolean key.a=key.b
 
 function hash(a:cached) int hash.key.a
 
 /function  ( knowsymbols:symboleset,processed:prg,sy:symbol) processed
  let q=mangledname.sy
  let sym = lookupsymbol(knowsymbols, q)
          assert isdefined.sym report"cannot locate" + q
          let b = if length.src.sym > 1 &and (src.sym)_1 in "parsedfunc Parsedfunc"then
          subseq(src.sym, 3 + toint.(src.sym)_2, length.src.sym)
          else src.sym
         let x=  bbbfirst(knowsymbols, b,  q, processed,resulttype.sym)
        let sig =    sig(name.sym, paratypes.sym, modname.sym, empty:seq.sig)
       let discard= encode(ecached,cached([q],sig))
       x

function bbb(knowsymbols:symbolset, s:seq.word, i:int, pending:seq.word, processed:prg, result:seq.sig)prg
  if i > length.s then
   if pending = "all"then processed else firstopt(processed, codedown.last.pending, result)
 else
   let this = s_i 
    let f1=findencode(ecached, cached(subseq(s,i,i+1),eqOp)) 
    if not.isempty.f1  &and i < length.s then
       bbb(knowsymbols, s, i + 2, pending, processed, result + s.(f1_1))
    else   
    let bb=if this ="LOCAL"_1  then sig( [ s_(i+1)], empty:seq.mytype, mytype."local", empty:seq.sig,mytype."?")
      else if this = "LIT"_1 then   lit.toint.s_(i+1)
      else if this = "WORD"_1 then wordsig.s_(i+1)
      else if this = "RECORD"_1 then  RECORD.toint.s_(i+1)
      else if this = "APPLY"_1 then  apply.toint.s_(i+1)
      else if this = "BLOCK"_1 then  block.toint.s_(i+1)
      else if this = "EXITBLOCK"_1 then  exit
      else if this = "BR"_1 then   br
      else if this = "DEFINE"_1 then  define.s_(i+1) 
      else eqOp
   if not(bb=eqOp) then  
     let discard=encode(ecached,cached([this,s_(i+1)],bb))
     bbb(knowsymbols, s, i + 2, pending, processed, result + bb)
    else   if this = "COMMENT"_1 then
    bbb(knowsymbols, s, i + 2 + toint.s_(i + 1), pending, processed, result)
   else if this = "IDXUC"_1 then bbb(knowsymbols, s, i + 1, pending, processed, result + IDXUC)
   else   if this = "SET"_1 then bbb(knowsymbols, s, i + 2, pending, processed, result)
   else if this = "WORDS"_1 then
    let l = toint.s_(i + 1)
    let name = subseq(s, i + 2, i + 1 + l)
     bbb(knowsymbols, s, i + 2 + toint.s_(i + 1), pending, processed, result + wordssig.name)
    else   if this="builtinZinternal1Zwordzseq"_1 then 
   // comment keeps this from being striped off //
   bbb(knowsymbols, s, i + 1, pending, processed, result)
   else 
      let q=if this = "FREF"_1 then s_(i+1) else this
      let f=findencode(ecached, cached([q],eqOp))  
      if not.isempty.f then  
      if this= "FREF"_1 then
            let newsig = sig("FREF" + q, empty:seq.mytype, mytype."$fref", [ s.(f_1)],mytype."?")
        bbb(knowsymbols, s, i + 2, pending, processed, result + newsig)
      else 
        bbb(knowsymbols, s, i + 1, pending, processed, result + s.(f_1))
     else  
      let d = codedown.q
     assert length.d > 1 report"BBB 3" + q
        let x= if q in pending &or  d_2 = "builtin" &or d_2=" local" &or last.d_2 = "para"_1 then   processed
         else
          let sym = lookupsymbol(knowsymbols, q)
          assert isdefined.sym report"cannot locate" + q
          let b = if length.src.sym > 1 &and (src.sym)_1 in "parsedfunc Parsedfunc"then
          subseq(src.sym, 3 + toint.(src.sym)_2, length.src.sym)
          else src.sym
           bbbfirst(knowsymbols, b,  pending + q, processed,resulttype.sym)
        let sig = if last.d_2 = "para"_1 then sig([ d_2_1], empty:seq.mytype, mytype."local", empty:seq.sig,mytype."?")
                  else if d_2 = "local"then sig(d_1, empty:seq.mytype, mytype."local", empty:seq.sig,mytype."?")
                  else      sig(d_1, @(+, mytype, empty:seq.mytype, subseq(d, 3, length.d)), mytype.d_2, empty:seq.sig,mytype."?")
       let discard= encode(ecached,cached([q],sig))
      if this= "FREF"_1 then
            let newsig = sig("FREF" + q, empty:seq.mytype, mytype."$fref", [ sig],mytype."?")
        bbb(knowsymbols, s, i + 2, pending, x, result + newsig)
      else 
        bbb(knowsymbols, s, i + 1, pending, x, result + sig)