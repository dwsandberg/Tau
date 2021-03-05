Module pass2

use UTF8

use bits

 
use interpreter

use real

use standard

use symbol

use words

use seq.char

use otherseq.int

use seq.int

use set.int

use otherseq.mytype

use seq.mytype

use otherseq.symbol

use seq.symbol

use set.symbol

use otherseq.word

use set.word

use otherseq.seq.int

use seq.seq.int

use seq.seq.symbol

use worddict.seq.symbol

use seq.seq.word

use set.seq.word

use seq.seq.seq.symbol

use mergeblocks

use graph.bbnode

use set.bbnode

function firstopt(p:program, s:symbol, code:seq.symbol, alltypes:typedict)seq.symbol
 if isempty.removeoptions.code then   code 
 else
  let nopara = nopara.s
  let pdict = addpara(emptyworddict:worddict.seq.symbol, nopara)
  let code1= removeoptions.code
  let b= tailrecusion(xxx(alltypes,p,toseq.nodes.mergeblocks.code1,s,pdict,length.code1),s)
  let a2 = scancode(alltypes,p, b, nopara + 1, pdict, true,s)
     fixoptions(s, a2,getoption.code) 
     
function xxx(alltypes:typedict,p:program,nodes:seq.bbnode,s:symbol,pdict:worddict.seq.symbol
,len:int) seq.bbnode
   let a=scancode(alltypes,p,  flattennodes(nodes,resulttype.s), nopara.s + 1, pdict, true,s)
   let r=   toseq.nodes.mergeblocks.code.a
   if   len=length.code.a &and (len > 20 &or  for same= length.nodes=length.r, idx=1, n = r while same do
         next( code.n=code.nodes_idx,idx+1) end (same))  then r
   else xxx(alltypes,p,r,s,pdict,length.code.a)
     
function tailrecusion(nodes:seq.bbnode,self:symbol) seq.symbol 
       let nopara=nopara.self      
       let norecursion=for  norecursion=true ,n= nodes  while norecursion do 
            kind.n &ne "exit"_1 &or (code.n)_-2 &ne  self  
       end (norecursion)
      if length.nodes=1  &or kind.(nodes)_1="loop"_1 &or norecursion &or nopara=0 then
         flattennodes(nodes,resulttype.self)
      else 
   let plist = for acc = empty:seq.symbol, e2 = arithseq(nopara, 1, 1)do 
      acc + Local.e2 end(acc)
 for acc=empty:seq.bbnode , n= nodes  do
      acc+if kind.n="exit"_1 &and (code.n)_-2 =self then
      bbnode(nodeno.n,adjustvar(code.n >> 2,nopara)+continue.nopara,"continue"_1,0,0)
      else 
      bbnode(nodeno.n,adjustvar(code.n,nopara),kind.n,brt.n,brf.n)
 end  (    let entrynode= bbnode(0,  plist 
 +Loopblock(paratypes.self,length.acc+1,nopara+1 ),"loop"_1,0,0 )
  flattennodes(acc+entrynode,resulttype.self))
     
 use seq.bbnode    
    
function adjustvar(s:seq.symbol, delta:int)seq.symbol
 for  acc=empty:seq.symbol, a =s do
    if islocal.a then
      acc+Local(toint.(fsig.a)_1 + delta) 
   else if isdefine.a then
      acc+Define.toword(toint.(fsig.a)_2 + delta) 
   else if isloopblock.a then
      acc+Loopblock(paratypes.a,noblocks.a,firstvar.a + delta)
     else acc+a
    end  (acc)

function print(s:seq.int)seq.word for acc ="", @e = s do acc + toword.@e end(acc)

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

   function scancode(alltypes:typedict,p:program, org:seq.symbol, nextvarX:int, mapX:worddict.seq.symbol
, apply:boolean,self:symbol)expandresult
     for   callsself=false,option="INLINE"_1,result=empty:seq.symbol,nextvar=nextvarX ,map=mapX, sym = org do
  let len = length.result
   if isconst.sym then 
      next(callsself, \\ if   isFref.sym &and not.isdefined.lookupcode(p, sym) then   "HASUNKNOWN"_1 else \\option, result + sym, nextvar, map)
   else if isspecial.sym then
     if \\ isdefine \\(fsig.sym)_1 = "DEFINE"_1 then
    let thelocal =(fsig.sym)_2
     if len > 0 ∧ (isconst.result_len ∨ islocal.result_len)then
     next(callsself,option, subseq(result, 1, length.result - 1), nextvar, replace(map, thelocal, [ result_len]))
     else
      next(callsself,option, result + Define.toword.nextvar, nextvar + 1, replace(map, thelocal, [ var.nextvar])) 
    else if isbr.sym then
       let hasnot=last.result=NotOp 
      let  sym1= if hasnot then Br2(brf.sym,brt.sym)  else sym
      let  result1 = if hasnot then result >> 1 else result
       let newsym=   if last.result1=Litfalse then Br2(brf.sym1,brf.sym1)
      else if last.result1=Littrue then Br2(brt.sym1,brt.sym1)
       else   sym1
         next(callsself,option,   result1 + newsym, nextvar, map)     
    else if isloopblock.sym then
      assert first.fsig.sym="LOOPBLOCK"_1 report "XXX"+fsig.sym
     let firstvar=if first.fsig.self="memcpy"_1 then 6   else
     assert  (fsig.sym)_3 &ne first."(" report "???} self:"+print.self+EOL+print.org
     firstvar.sym
    let nopara = nopara.sym
       next(callsself,option,  result+ Loopblock(paratypes.sym,noblocks.sym,nextvar )
     , nextvar + nopara, addlooplocals(map, firstvar, nextvar, nopara, 0))
    else if isRecord.sym ∨ isSequence.sym then
    let nopara = nopara.sym
    let args = subseq(result, len + 1 - nopara, len)
      let constargs=for acc = true, @e = args while acc do 
            isconst.@e end(acc) \\  &and   
            not.isFref.@e &or    isdefined.lookupcode(p,(constantcode.@e)_1) 
          end(acc) \\
     if constargs then
     next(callsself,option, subseq(result, 1, len - nopara) + Constant2(args + sym), nextvar, map)
     else next(callsself,option, result + sym, nextvar, map)
    else if(module.sym)_1 = "local"_1 then
    let t = lookup(map,(fsig.sym)_1)
       next(callsself,option, result + if isempty.t then [sym] else  t_1, nextvar, map)
    else if(module.sym)_1 = "para"_1 then
    let sym2 = Local.(module.sym)_2
    let t = lookup(map,(fsig.sym2)_1)
     if isempty.t then next(callsself,option, result +if isempty.t then [sym] else  t_1, nextvar, map)
     else next(callsself,option, result + t_1, nextvar, map)
    else  next(callsself,option, result + sym, nextvar, map) 
   else  if length.result > 2 &and isconst.last.result &and  islocal.result_-2
    &and fsig.sym ∈ ["∈(int, int seq)","∈(word, word seq)"] then 
     next(callsself,option ,result >> 2 +removeismember(last.result,result_-2),nextvar,map)
   else if   (fsig.sym)_1 ∈ "forexp"then 
     let noop=forexpisnoop(sym,result)
    if not.isempty.noop then 
       next(callsself,option, noop, nextvar, map)
    else    if apply then 
    let f=forexpcode(sym, result, nextvar)
    next(callsself,option, code.f, nextvar.f, map)
    else
    next(callsself,option,   result + sym, nextvar, map)
   else if sym=self then  next(true,option ,result+sym,nextvar,map)
   else
    let nopara = nopara.sym
    let dd1=lookupcode(p, sym)
    if not.isdefined.dd1   then 
    let newoption= if  (fsig.sym)_1 ∈ "setfld" ∨ module.sym = "$global"
         then"STATE"_1  else if sym=Optionsym &or first.fsig.sym ∈ "toseq" then option else "HASUNKNOWN"_1
         next(callsself,newoption ,result+sym,nextvar,map)
       else 
    let dd = code.dd1
    let options = getoption.dd
     if(first."COMPILETIME" ∈ options ∨ fsig.sym = "_(word seq, int)")
     ∧ for acc = true, @e = subseq(result, len - nopara + 1, len)do acc ∧ isconst.@e end(acc)then
    \\ assert  fsig.sym &ne "_(word seq, int)"  report "XXXXXXX" \\
     let newcode = interpretCompileTime(alltypes,subseq(result, len - nopara + 1, len) + sym)
     let newconst = if length.newcode > 1 then Constant2.newcode else first.newcode
       next(callsself,option, result >> nopara + newconst, nextvar, map)
     else if fsig.sym = "decodeword(word)" ∧ module.result_len = "$word"then
     let arg1 = result_len
     let a1 = for acc = empty:seq.symbol, @e = tointseq.decodeword.(fsig.arg1)_1 do acc + Lit.@e end(acc)
     let d = Constant2(a1 + Sequence(typeint, length.a1))
      next(callsself,option, result >> 1 + d, nextvar, map)
     else if not("INLINE"_1 ∈ options ∨ first."VERYSIMPLE" ∈ options)then
         let newoption= if "STATE"_1 ∈ options ∨(fsig.sym)_1 ∈ "setfld" ∨ module.sym = "$global"
         then"STATE"_1 else option 
     next( sym=self &or callsself,newoption,   result + sym, nextvar, map)
     else
      let code = removeoptions.dd
       if isempty.code then next(callsself,option, result + sym, nextvar, map)
       else if length.code = 1 ∧ code = [ var.1] ∧ nopara = 1 then
       \\ function just returns result \\ next(callsself,option, result, nextvar, map)
       else
        let t = backparse(result, len, nopara, empty:seq.int) + [ len + 1]
        \\ assert length.t = nopara + 1 report"INLINE PARA PROBLEM" \\
         let new = if issimple( nopara, code)then
         let pmap = simpleparamap(result, t, emptyworddict:worddict.seq.symbol, nopara)
          scancode(alltypes,p, code,  nextvar, pmap,apply,self)
         else expandinlineX(alltypes,result, t, emptyworddict:worddict.seq.symbol, nopara, empty:seq.symbol, nextvar, code, p,apply,self)
          let newoption=if option="INLINE"_1 then last.options.new else
           if option="HASUNKNOWN"_1 then option
           else if "HASUNKNOWN"_1=last.options.new then "HASUNKNOWN"_1
           else "STATE"_1
          next(callsself &or "CALLSSELF"_1=first.options.new ,newoption, subseq(result, 1, t_1 - 1) + code.new, nextvar.new, map)
    end( expandresult(nextvar, result, if callsself then "CALLSSELF"+option else [option]))

function issimple( nopara:int, code:seq.symbol)boolean
    for   last=0, rep =code  while last > -1 do 
      if islocal.rep then
        let parano = value.rep
         if parano = last + 1  &and parano &le nopara then  parano 
         else  -1 
       else if isdefine.rep &or isloopblock.rep then -1
       else  last 
    end (     last = nopara     )


function simpleparamap(s:seq.symbol, t:seq.int, pmap:worddict.seq.symbol, i:int)worddict.seq.symbol
 if i = 0 then pmap
 else
  simpleparamap(s, t, add(pmap, toword.i, subseq(s, t_i, t_(i + 1) - 1)), i - 1)

function expandinlineX(alltypes:typedict,s:seq.symbol, t:seq.int, pmap:worddict.seq.symbol, i:int, newcode:seq.symbol, nextvar:int, inlinecode:seq.symbol, p:program, papply:boolean,self:symbol)expandresult
 \\ when i > 0 then assigning parameters to new local variables \\
 if i = 0 then
 let r = scancode(alltypes,p, inlinecode, nextvar, pmap, papply,self)
  expandresult(nextvar.r, newcode + code.r,options.r)
 else
  expandinlineX(alltypes,s, t, add(pmap, toword.i, [ var.nextvar]), i - 1, subseq(s, t_i, t_(i + 1) - 1) + Define.toword.nextvar + newcode, nextvar + 1, inlinecode, p, papply,self)

function replace(s:seq.symbol, start:int, length:int, value:seq.symbol)seq.symbol
 subseq(s, 1, start - 1) + value + subseq(s, start + length, length.s)

function adddefines2(s:seq.symbol, t:seq.int, i:int, nopara:int, newcode:seq.symbol, nextvar:int)seq.symbol
 if i > nopara then newcode
 else
  adddefines2(s, t, i + 1, nopara, newcode + subseq(s, t_i, t_(i + 1) - 1)
  + Define.toword(nextvar + i - 1), nextvar)

type expandresult is nextvar:int, code:seq.symbol,options:seq.word

function definepara(code:seq.symbol, t:seq.int, i:int, nextvar:int, newcode:seq.symbol)seq.symbol
 if i = 0 then newcode
 else
  definepara(code, t, i - 1, nextvar - 1, subseq(code, t_i, t_(i + 1) - 1) + Define.toword.nextvar + newcode)

compound accumaltor possiblities
+(int graph, int arc)graph.int
,"advancepnp(pnpstate, word)format"
,"state100(state100, program, symbol, symbol)breakblocks"
,"+(out23, char)format"
,"deletearc(word seq graph, word seq arc)graph.seq.word"
,"+(word seq graph, word seq arc)graph.seq.word"
,"+(place, char seq encodingpair)maindict"] 


function forexpisnoop (forsym:symbol,code:seq.symbol) seq.symbol
if nopara.forsym=7  ∧ code_(-2) = Littrue 
   ∧  abstracttype.resulttype.last.code = "seq"_1  
 ∧  name.code_-3 = "+"
 ∧  last.module.code_-3 = "seq"_1
 ∧ name.code_-4 = "SEQUENCE 1" 
 ∧ last.code = code_-8
 ∧ last.code = code_-6
 &and  code_-7=code_-5 then 
let t2 = backparse(code, length.code-8, 2, empty:seq.int)
let initacc = subseq(code, t2_1, t2_2 - 1)
 if length.initacc = 1 ∧ isrecordconstant.initacc_1
 ∧ constantcode.initacc_1 = [ Lit.0, Lit.0]then
 subseq(code, 1, t2_1 - 1) + subseq(code, t2_2, length.code-8)
 else empty:seq.symbol
else empty:seq.symbol

function forexpcode( forsym:symbol, code:seq.symbol, nextvar:int)expandresult
let t = backparse(code, length.code, 4, empty:seq.int)
let endexp = subseq(code, t_(-1), length.code)
let exitexp = subseq(code, t_(-2), t_(-1) - 1)
let bodyexp = subseq(code, t_(-3), t_(-2) - 1)
let endofsymbols = t_(-3) - 1
let startofsymbols = endofsymbols - (nopara.forsym - 3) / 2 + 1
let syms = subseq(code, startofsymbols, endofsymbols)
let tmp = for acc = empty:seq.symbol, i = 1, s = syms >> 1 do
 next(acc + Local(nextvar + i - 1), i + 1)
end(acc)
let masteridx = Local(value.last.tmp + 1)
let seqelement = Local(value.masteridx + 1)
let nextvar1 = value.seqelement + 1
let Defineseqelement = Define.fsig.seqelement
let newsyms = tmp + seqelement
let theseqtype =(paratypes.forsym)_(length.newsyms)
let elementtype = if abstracttype.parameter.theseqtype ∈ "real"then mytype."real"
else if abstracttype.parameter.theseqtype ∈ "int bit byte boolean"then typeint else typeptr
let packedseq = maybepacked.theseqtype
let theseq = Local.nextvar1
let totallength = Local(nextvar1 + 1)
let seqtype = Local(nextvar1 + 2)
let Defineseqtype = Define(nextvar1 + 2)
  let blkadjust=if isblock.last.bodyexp &and abstracttype.parameter.modname.last.bodyexp ="$base"_1 then
           nopara.last.bodyexp -1 else 0
  let bodyexp2=replace$for(bodyexp, newsyms, syms)
  let bodyexp3=if length.syms = 2 then 
         bodyexp2+[ masteridx, Lit.1, PlusOp, continue.2]
         else if blkadjust=0 then
          bodyexp2  >> 1+[ masteridx, Lit.1, PlusOp, continue.length.syms]
         else 
            let back2=   backparse(bodyexp2, length.bodyexp2-1, blkadjust+1, empty:seq.int) +length.bodyexp2
            for acc=empty:seq.symbol,last=length.bodyexp2, b = back2  do  
              let clause=subseq(bodyexp2,last,b-1)
              let clause2=if length.clause=0 then clause
                  else if isbr.last.clause  then
                               clause >> 1+Br2( 4+brt.last.clause , 4+brf.last.clause)
                  else if last.clause=Exit then 
                   clause >> 2 +if module.clause_-2="$for" then
                       [ masteridx, Lit.1, PlusOp, continue.length.syms]
                     else   
                         let typ=resulttype.forsym
                         let typ2=if abstracttype.typ="seq"_1 then "ptr"
                         else typerep.typ
                       [symbol("assert:"+typ2+"(word seq)" ,
                               "builtin",typ2),Exit]
                  else clause 
                next(acc+ clause2 ,b)
            end (acc)
let newcode=  
 subseq(code, 1, startofsymbols - 1) + Define.nextvar1 + theseq + GetSeqLength
  + Define(nextvar1 + 1)
  + Lit.1
  + Loopblock(subseq(paratypes.forsym, 1, length.syms - 1) + typeint,5+blkadjust,nextvar)
  + \\ 2 if masteridx > totallength then exit \\
  [ masteridx, totallength, GtOp ]+Br2(4,3)  
  +\\ 3 else let sequenceele = seq_(idx)\\ 
       [theseq, GetSeqType, Defineseqtype, seqtype, Lit.0, EqOp]+Br2(2,3)  
   +[ theseq, masteridx, IdxS.theseqtype, Exit]
  + if packedseq then [ seqtype, Lit.1, EqOp]+Br2(4,5)  
    +   [ theseq, masteridx] + packedindex2.theseqtype + [ Exit]
  else empty:seq.symbol fi
  + [ theseq, masteridx, Callidx.theseqtype, Exit, 
     Block(elementtype, if packedseq then 5 else 3)]
  + [ Defineseqelement]
  + \\ 3 while condition \\
  replace$for(exitexp, newsyms, syms) +Br2(5,4)  
   + \\ 4 exit loop \\
  replace$for(endexp, newsyms, syms)+  Exit
  + \\ 5 do body and continue \\
    bodyexp3
   + [ Block(resulttype.forsym, 5+blkadjust)]
  \\   assert false report print.forsym + print.startofsymbols + print.endofsymbols + EOL + print.endexp + EOL +"exit:"+ print.exitexp + EOL +"body:"+ print.bodyexp + EOL +"syms"+ print.subseq(code, startofsymbols, endofsymbols)+ EOL +"part1"+ print.part1 
  \\  expandresult(nextvar1 + 3,newcode, "" )
  
  

function replace$for(code:seq.symbol, new:seq.symbol, old:seq.symbol)seq.symbol 
for acc = empty:seq.symbol,  s = code do 
      acc+if last.module.s = "$for"_1 then
        let i = findindex(s, old)
         if i ≤ length.new then [ new_findindex(s, old)]
         else \\  this is for one of two cases 1: a nested for and $for variable is from outer loop 
           2: the next expresion \\ [ s]
      else [s]
 end(acc)
        
     


function maxvarused(code:seq.symbol)int maxvarused(code, 1, 0)

function maxvarused(code:seq.symbol, i:int, lastused:int)int
 if i > length.code then lastused
 else
  let s = code_i
   maxvarused(code
   , i + 1
   , max(lastused
   , if abstracttype.modname.s = "local"_1 then toint.(fsig.s)_1
   else if abstracttype.modname.s = "$define"_1 then toint.(fsig.s)_2 else 0
   )
   )

function depthfirst(knownsymbols:program, alltypes:typedict, i:int, pending:seq.symbol, processed:program, code:seq.symbol, s:symbol)program
 if i > length.code then 
   map(processed,s,firstopt(processed, s, code, alltypes))
 else
  let sym = code_i
  let sym2 = basesym.sym
  let newprg = if isconst.sym2 ∨ isspecial.sym2 ∨ sym2 ∈ pending 
  then processed
  else
   let r = lookupcode(processed, sym)
    if isdefined.r then processed
    else
     let rep2 = lookupcode(knownsymbols, sym2)
      if length.code.rep2 > 0 then 
   depthfirst(knownsymbols, alltypes, 1, pending + sym2, processed, code.rep2, sym2)
   else processed
   depthfirst(knownsymbols, alltypes, i + 1, pending, newprg, code, s)
   
   

________________________________


function fixoptions( s:symbol, e:expandresult,options:seq.word) seq.symbol
let code0=code.e
let code = removeoptions.code0
let fsig = fsig.s
let newoptions = if fsig = "∈(int, int seq)" ∨ fsig = "∈(word, word seq)"
∨ fsig = "_(int seq, int)"
∨ fsig = "_(word seq, int)"then
""
else
 let c= if  "INLINE"_1  &nin options.e  ∧ "STATE"_1 ∉ options then "STATE" else "" fi
     + if length.code < 20 ∧ first.options.e &ne "CALLSSELF"_1 ∧ "NOINLINE"_1 ∉ options 
      ∧ "INLINE"_1 ∉ options   then
       "INLINE"
    else ""
     options+c
  if newoptions = ""then code else code + Words.newoptions + Optionsym 

 

---------------------------

Function pass2(knownsymbols:program, alltypes:typedict)program
  \\  ttt1(knownsymbols,alltypes,emptyprogram,emptyprogram)    \\
let bin0 =       filterp2(emptyprogram, emptyprogram,toseq.knownsymbols, knownsymbols,alltypes)
let bin =   filterp2(emptyprogram, core.bin0,toseq.big.bin0, big.bin0,alltypes)
 \\ assert false report checkt(bin0)assert false report print.length.toseq.big.bin + print.length.toseq.core.bin \\
 for acc = core.bin, sym = toseq.big.bin do
  \\ depthfirst(acc, knownsymbols, alltypes, sym)Function depthfirst(acc:program, knownsymbols:program, alltypes:typedict, sym:symbol)program \\
  depthfirst(acc, alltypes, 1, [ sym], acc, code.lookupcode(knownsymbols, sym), sym)
 end(acc)

type filterp is big:program, small:program,core:program

function filterp2(big1:program,core1:program,q:seq.symbol,z:program,alltypes:typedict) filterp
    for big=big1,small=emptyprogram, core=core1 , s = q do  
     let fullcode=code.lookupcode(z, s)
     let options = getoption.fullcode
     let  code       = removeoptions.fullcode
 if isempty.code ∨ "BUILTIN"_1 ∈ options ∨ "VERYSIMPLE"_1 ∈ options then
          next(big, small,map(core, s, fullcode))
 else if length.code < 30 ∨ "COMPILETIME"_1 ∈ options then
    let code4=firstopt(core, s, fullcode, alltypes)
    if   "STATE"_1 &in getoption.code4  ∧ "COMPILETIME"_1 ∉ options then
         next(map(big,s,code4),small, core)
        else 
          next(big,small, map(core,s,code4))
     else 
       next(map(big, s, code),small, core)
     end(filterp(big,core,core))
     
function ttt1(   z:program,alltypes:typedict,bigin:program,corein:program)  program
  let r=  for  big=bigin,small=emptyprogram,core=corein,s=toseq.z do
           let fullcode=code.lookupcode(z, s)
           let options = getoption.fullcode
           let  code       = removeoptions.fullcode
        if isempty.code ∨ "BUILTIN"_1 ∈ options ∨ "VERYSIMPLE"_1 ∈ options then
              next(big,small, map(core, s, fullcode))
           else  if length.fullcode < 30 &or  "COMPILETIME"_1 &in options then
              let code4=firstopt(small,s,fullcode,alltypes)
              let newoption= getoption.code4
              if "STATE"_1 &in newoption ∧ "COMPILETIME"_1 ∉ options &or length.code4 &ge 30
                then
                  next(big,map(small,s,code4),core) 
                else  
                  next(big,map(small,s,code4),map(core,s,code4)) 
            else next(map(big,s,fullcode),small,core)
       end( filterp(big,small,core))
        if  length.toseq.corein &ne length.toseq.core.r then
               ttt1(small.r,alltypes,big.r,core.r)
             else 
    let p=big.r &cup small.r
for acc = core.r, sym = toseq.p do
   depthfirst(acc, alltypes, 1, [ sym], acc, code.lookupcode(p, sym), sym)
 end(acc)     

function backparse(s:seq.symbol, i:int, no:int, result:seq.int)seq.int
 if no = 0 then result
 else
  assert i > 0 report"back parse 1:" + toword.no + print.s + stacktrace
   if isdefine.s_i then
   let args = backparse(s, i - 1, 1, empty:seq.int)
    backparse(s, args_1, no, result)
   else
    let nopara = nopara.s_i
    let first = if nopara = 0 then i
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

function removeismember(c:symbol,var:symbol) seq.symbol
 if module.c="$words" then 
    let words= fsig.c
    if isempty.words then [Litfalse] else 
    let t=length.words+1
    if length.words=1 then [var,Word.words_1,EqOp] 
    else
     for acc=empty:seq.symbol,idx=2,w = words >> 1   do 
         next(acc+[var,Word.w,EqOp]+Br2(t,idx) ,idx+1)
     end(acc+[var,Word.last.words,EqOp,Exit,Littrue,Exit,Block(mytype."boolean",t)])
  else
     let z=constantcode.c << 2
     if isempty.z then [Litfalse] else
     let t=length.z+1
     for acc=empty:seq.symbol,idx=2,w = z >> 1   do 
       next(acc+[var,w,EqOp]+  Br2( t, idx  ) ,idx+1)
      end(acc+[var, last.z,EqOp,   Exit,Littrue,Exit
              ,Block(mytype."boolean",t)])
 


Function uses(p:program, roots:set.symbol)set.symbol uses(p, empty:set.symbol, roots)

Function defines(p:program, roots:set.symbol)seq.symbol
 for acc = empty:seq.symbol, @e = toseq.roots do
  acc + if isconstantorspecial.@e ∨ isabstract.modname.@e then empty:seq.symbol else [ @e]
 end(acc)

function uses(p:program, processed:set.symbol, toprocess:set.symbol)set.symbol
 if isempty.toprocess then processed
 else
  let q = asset.for acc = empty:seq.symbol, @e = toseq.toprocess do
   acc
  + let d = code.lookupcode(p, @e)
   \\ assert not.containspara.d report"has p"+ print.@e + print.d \\
    if isempty.d then constantcode.@e else d
  end(acc)
   uses(p, processed ∪ toprocess, q - processed)

function containspara(code:seq.symbol)boolean for hasparameter = false, e = code do hasparameter ∨ isparameter.e end(hasparameter)