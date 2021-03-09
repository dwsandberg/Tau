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


use mergeblocks2


function firstopt(p:program, s:symbol, code:seq.symbol, alltypes:typedict) expandresult
    let pdict= for   pmap=emptyworddict:worddict.seq.symbol,parano=1, e=constantseq(10000,1) while  parano &le nopara.s do 
           next(add(pmap, toword.parano, [ Local.parano]),parano+1)
     end(pmap)
   xxx(alltypes,p,removeoptions.code,s,pdict,true)  
     
 function xxx(alltypes:typedict,p:program,code:seq.symbol,s:symbol,
 pdict:worddict.seq.symbol,first:boolean
) expandresult
     let a=scancode(alltypes,p,  code, nopara.s + 1, pdict, s)
      let new=if Hasmerge &in flags.a then undoR.optB(cvtR.code.a ,Lit.1) else code.a
     if  length.code=length.new &and length.code > 20 &or new=code then 
        \\ expandresult(nextvar.a,undoR.optB(cvtR.code.z,s),options.z) \\ 
        let new1= if    Hasfor &in flags.a  then expandforexp(new,nextvar.a) else new
         let t= if Callself &in  flags.a  
          &and  (fsig.s)_1 &ne"subpass2"_1 then optB(cvtR.new1,s) else cvtR.new1
         let t2= if length.t > 0 &or  Exit &nin t  then undoR(t,false) 
           else  if  (length.t < 13  ) &or  fsig.s &in ["firstword(bitstream)","xt033","between(int, int, int)"
           ,"hasunbound(firstpass)","seperator(char seq, char, char seq)","xseperator(word seq, word seq)"]  then undoR(t,true)
           else 
             assert true   report "HJK"+print.s  +print.undoR(t,true) 
               undoR(t,false) 
        \\ let z=undoR(t,true)
         assert      fsig.s &ne "result(runitresult process)" report "DIFF "+print.s +print.z \\
         expandresult(nextvar.a, t2 ,flags.a)
     else 
     xxx(alltypes,p,new,s,pdict,true)
    

function print(s:seq.int)seq.word for acc ="", @e = s do acc + toword.@e end(acc)

 
    

function addlooplocals(map:worddict.seq.symbol, firstvar:int, nextvar:int, nopara:int)worddict.seq.symbol
     for   pmap=map,parano=1, e=constantseq(10000,1) while  parano &le nopara  do 
           next(replace(pmap, toword(firstvar+parano-1), [ Local(nextvar+parano-1)]),parano+1)
     end(pmap)

  
 Function  Callself bits bits.1
 
 Function Hasunknown bits bits.2
 
 Function State bits bits.4
 
 Function Hasfor bits bits.8
 
 Function Hasmerge bits bits.16
 
 function  &in(a:bits,b:bits) boolean  (a &and b )=a

   function scancode(alltypes:typedict,p:program, org:seq.symbol, nextvarX:int, mapX:worddict.seq.symbol
, self:symbol)expandresult
     for   flags=bits.0,result=empty:seq.symbol,nextvar=nextvarX ,map=mapX, sym = org do
  let len = length.result
   if isconst.sym then 
      next(flags, \\ if   isFref.sym &and not.isdefined.lookupcode(p, sym) then   "HASUNKNOWN"_1 else \\ result + sym, nextvar, map)
   else if isspecial.sym then
     if \\ isdefine \\(fsig.sym)_1 = "DEFINE"_1 then
    let thelocal =(fsig.sym)_2
     if len > 0 ∧ (isconst.result_len ∨ islocal.result_len)then
     next(flags, subseq(result, 1, length.result - 1), nextvar, replace(map, thelocal, [ result_len]))
     else
      next(flags, result + Define.toword.nextvar, nextvar + 1, replace(map, thelocal, [ Local.nextvar])) 
    else if isbr.sym then
       let hasnot=last.result=NotOp 
      let  sym1= if hasnot then Br2(brf.sym,brt.sym)  else sym
      let  result1 = if hasnot then result >> 1 else result
       let newsym=   if last.result1=Litfalse then Br2(brf.sym1,brf.sym1)
      else if last.result1=Littrue then Br2(brt.sym1,brt.sym1)
       else   sym1
         next(flags,   result1 + newsym, nextvar, map) 
     else if sym=Exit &and isblock.last.result then
      next(  flags &or Hasmerge , result+sym,nextvar,map)  
    else if isloopblock.sym then
      let nopara = nopara.sym
       next(flags,  result+ Loopblock(paratypes.sym,nextvar,resulttype.sym )
     , nextvar + nopara, addlooplocals(map, firstvar.sym, nextvar, nopara ))
    else if isRecord.sym ∨ isSequence.sym then
    let nopara = nopara.sym
    let args = subseq(result, len + 1 - nopara, len)
      let constargs=for acc = true, @e = args while acc do 
            isconst.@e end(acc) \\  &and   
            not.isFref.@e &or    isdefined.lookupcode(p,(constantcode.@e)_1) 
          end(acc) \\
     if constargs then
     next(flags, subseq(result, 1, len - nopara) + Constant2(args + sym), nextvar, map)
     else next(flags, result + sym, nextvar, map)
    else if(module.sym)_1 = "local"_1 then
    let t = lookup(map,(fsig.sym)_1)
       next(flags, result + if isempty.t then [sym] else  t_1, nextvar, map)
    else if(module.sym)_1 = "para"_1 then
    let sym2 = Local.(module.sym)_2
    let t = lookup(map,(fsig.sym2)_1)
     if isempty.t then next(flags, result +if isempty.t then [sym] else  t_1, nextvar, map)
     else next(flags, result + t_1, nextvar, map)
    else  next(flags, result + sym, nextvar, map) 
   else  if length.result > 2 &and isconst.last.result &and  islocal.result_-2
    &and fsig.sym ∈ ["∈(int, int seq)","∈(word, word seq)"] then 
     next(flags, result >> 2 +removeismember(last.result,result_-2),nextvar,map)
   else if   (fsig.sym)_1 ∈ "forexp" &and module.sym="builtin"  then 
     let noop=forexpisnoop(sym,result)
    if not.isempty.noop then 
       next(flags, noop, nextvar, map)
    else    
       next(  flags  &or Hasfor   ,    result + sym, nextvar, map)
   else if sym=self then  next(flags &or Callself,result+sym,nextvar,map)
   else
    let nopara = nopara.sym
    let dd1=lookupcode(p, sym)
    if not.isdefined.dd1   then 
          let newflags=if  (fsig.sym)_1 ∈ "setfld" ∨ module.sym = "$global" then State else bits.0 fi 
         &or if sym=Optionsym &or first.fsig.sym ∈ "toseq" then bits.0 else Hasunknown    
         next(flags &or newflags ,result+sym,nextvar,map)
       else 
    let dd = code.dd1
    let options = getoption.dd
     if(first."COMPILETIME" ∈ options ∨ fsig.sym = "_(word seq, int)")
     ∧ for acc = true, @e = subseq(result, len - nopara + 1, len)do acc ∧ isconst.@e end(acc)then
    \\ assert  fsig.sym &ne "_(word seq, int)"  report "XXXXXXX" \\
     let newcode = interpretCompileTime(alltypes,subseq(result, len - nopara + 1, len) + sym)
     let newconst = if length.newcode > 1 then Constant2.newcode else first.newcode
       next(flags, result >> nopara + newconst, nextvar, map)
     else if fsig.sym = "decodeword(word)" ∧ module.result_len = "$word"then
     let arg1 = result_len
     let a1 = for acc = empty:seq.symbol, @e = tointseq.decodeword.(fsig.arg1)_1 do acc + Lit.@e end(acc)
     let d = Constant2(a1 + Sequence(typeint, length.a1))
      next(flags, result >> 1 + d, nextvar, map)
     else if not("INLINE"_1 ∈ options ∨ first."VERYSIMPLE" ∈ options)then
         let  newflags= if "STATE"_1 ∈ options ∨(fsig.sym)_1 ∈ "setfld" ∨ module.sym = "$global"
         then State &or flags else flags
     next( newflags,   result + sym, nextvar, map)
     else
      let code = removeoptions.dd
       if isempty.code then next(flags, result + sym, nextvar, map)
       else if length.code = 1 ∧ code = [ Local.1] ∧ nopara = 1 then
       \\ function just returns result \\ next(flags, result, nextvar, map)
       else
        let t = backparse(result, len, nopara, empty:seq.int) + [ len + 1]
        \\ assert length.t = nopara + 1 report"INLINE PARA PROBLEM" \\
         let new = if issimple( nopara, code)then
            for  simpleparamap=emptyworddict:worddict.seq.symbol,     parano=1,  lastidx=t_1,  idx = t << 1 do
               next(  add(simpleparamap,toword.parano,subseq(result, lastidx,idx-1)),parano+1,idx) 
            end(scancode(alltypes,p, code,  nextvar, simpleparamap,self))
         else expandinline(alltypes,result, t, nextvar, code, p,self)
           next( flags &or flags.new,subseq(result, 1, t_1 - 1) + code.new, nextvar.new, map)
    end( 
      let match=if (flags &and Hasunknown ) =Hasunknown then "HASUNKNOWN" else 
         if (flags &and State) = State then "STATE" else "INLINE" 
       expandresult(nextvar, result,flags))

function issimple( nopara:int, code:seq.symbol)boolean
    for   last=0, rep =code  while last > -1 do 
      if islocal.rep then
        let parano = value.rep
         if parano = last + 1  &and parano &le nopara then  parano 
         else  -1 
       else if isdefine.rep &or isloopblock.rep then -1
       else  last 
    end (     last = nopara     )

   
 function expandinline(alltypes:typedict,s:seq.symbol, t:seq.int, nextvarin:int, inlinecode:seq.symbol, p:program, self:symbol)expandresult 
  for  pmap=emptyworddict:worddict.seq.symbol,  code=empty:seq.symbol, nextvar=nextvarin,  parano=1,  lastidx=t_1,  idx = t << 1 do
       next(  add(pmap,toword.parano,[Local.nextvar])
       ,code+subseq(s, lastidx,idx-1) + Define.toword.nextvar  
       ,nextvar+1,parano+1,idx) end(
        let r=scancode(alltypes,p, inlinecode, nextvar, pmap, self) 
          expandresult(nextvar.r, code + code.r,flags.r)  )
   

function replace(s:seq.symbol, start:int, length:int, value:seq.symbol)seq.symbol
 subseq(s, 1, start - 1) + value + subseq(s, start + length, length.s)

function adddefines2(s:seq.symbol, t:seq.int, i:int, nopara:int, newcode:seq.symbol, nextvar:int)seq.symbol
 if i > nopara then newcode
 else
  adddefines2(s, t, i + 1, nopara, newcode + subseq(s, t_i, t_(i + 1) - 1)
  + Define.toword(nextvar + i - 1), nextvar)

type expandresult is nextvar:int, code:seq.symbol, flags:bits


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

function expandforexp(code:seq.symbol,nextvarin:int) seq.symbol
  for  result=empty:seq.symbol, nextvar=nextvarin,sym=code do
   if last.module.sym="builtin"_1   &and  (fsig.sym)_1 = "forexp"_1 then 
    let   f=forexpcode(sym, result, nextvar)
   next(  code.f, nextvar.f) 
   else next(result+sym,nextvar)
 end(result)

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
let temp=abstracttype.parameter.theseqtype
let elementtype = if temp ∈ "real boolean"then mytype.[temp]
else if temp ∈ "int bit byte boolean"then typeint 
else typeptr
let packedseq = maybepacked.theseqtype
let theseq = Local.nextvar1
let totallength = Local(nextvar1 + 1)
let seqtype = Local(nextvar1 + 2)
let Defineseqtype = Define(nextvar1 + 2)
let firstpart=  
 subseq(code, 1, startofsymbols - 1) + Define.nextvar1 + theseq + GetSeqLength
  + Define(nextvar1 + 1)
  + Lit.1
  + Loopblock(subseq(paratypes.forsym, 1, length.syms - 1) + typeint,nextvar,resulttype.forsym)
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
let bodyexp2=replace$for(bodyexp, newsyms, syms)
let lastpart= if length.syms = 2 then
 bodyexp2+[ masteridx, Lit.1, PlusOp, continue.2,Block(resulttype.forsym, 5)]
else 
  let iscompound = isblock.last.bodyexp &and abstracttype.parameter.modname.last.bodyexp ="$base"_1
   if not.iscompound then   
           bodyexp2  >> 1+[ masteridx, Lit.1, PlusOp, continue.length.syms,Block(resulttype.forsym, 5)]
else 
   let back2=   backparse(bodyexp2, length.bodyexp2-1, nopara.last.bodyexp, empty:seq.int) +length.bodyexp2       
           for acc=empty:seq.symbol,last=length.bodyexp2,count=5, b = back2  do  
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
                next(acc+ clause2 ,b,if isempty.acc then count else count+1)
            end (   acc+   Block(resulttype.forsym, count) )
   expandresult(nextvar1 + 3,firstpart+lastpart, bits.0 )
  
  

function replace$for(code:seq.symbol, new:seq.symbol, old:seq.symbol)seq.symbol 
for acc = empty:seq.symbol,  s = code do 
      acc+if last.module.s = "$for"_1 then
        let i = findindex(s, old)
         if i ≤ length.new then [ new_i]
         else \\  this is for one of two cases 1: a nested for and $for variable is from outer loop 
           2: the next expresion \\ [ s]
      else [s]
 end(acc)
        
     




function depthfirst(knownsymbols:program, alltypes:typedict, i:int, pending:seq.symbol, processed:program, code:seq.symbol, s:symbol)program
 if i > length.code then 
   map(processed,s,fixoptions(s,firstopt(processed, s, code, alltypes),getoption.code))
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
 let c= if  (State &in flags.e &or Hasunknown &in flags.e )  ∧ "STATE"_1 ∉ options then "STATE" else "" fi
     + if length.code < 20 ∧ Callself &nin flags.e    ∧ "NOINLINE"_1 ∉ options 
      ∧ "INLINE"_1 ∉ options   then
       "INLINE"
    else ""
     options+c
  if newoptions = ""then code else code + Words.newoptions + Optionsym 

 

---------------------------

Function pass2(knownsymbols:program, alltypes:typedict)program
subpass2(alltypes,empty:seq.programele,emptyprogram,knownsymbols,0)

\\let h=for    acc="",      e=toseq.knownsymbols do   if target.lookupcode(knownsymbols,e) = e 
then "" else print.e end(acc)
 assert isempty.h report "HJK"+h\\
 
use seq.programele

SIZE 2283 868 1385 1
SIZE 1646 1080 1810 2
SIZE 1589 1103 1844 3
SIZE 1584 1108 1844 4

SIZE 1751 918 1867 4

SIZE 2333 315 1888 4

function  subpass2(  alltypes:typedict,  bigin:seq.programele,corein:program,toprocess:program,count:int) program
\\  assert   count < 4 report "SIZE"+ print.length.toseq.toprocess+print.length.bigin
   +print.length.toseq.corein+print.count
\\  for  big=bigin,small=emptyprogram,core=corein , pele = toseqprogramele.toprocess do 
     let s=target.pele 
     let fullcode=code.pele
     let options = getoption.fullcode
     let  code       = removeoptions.fullcode
    if isempty.code ∨ "BUILTIN"_1 ∈ options ∨ "VERYSIMPLE"_1 ∈ options then
           next(big,small,map(core, s, fullcode))
     else if "COMPILETIME"_1 ∈ options then
       let code4=fixoptions(s,firstopt(core, s, fullcode, alltypes),options)
        next(big,small,map(core, s, code4))
     else if length.code < 30 then 
         let t=firstopt(core, s, fullcode, alltypes)  
           if   Hasunknown  &nin  flags.t   then 
              next(big,small,map(core,s,fixoptions(s,t,options)) )
           else 
             next(big,map(small,s, if isempty.options then  code.t else  code.t+subseq(fullcode,length.fullcode-1,length.fullcode)),core)
     else next(big+pele,small,core)
  end( if   length.toseq.corein=length.toseq.core  then
    for acc = core &cup small, prgele= big do
   depthfirst(acc, alltypes, 1, [target.prgele], acc, code.prgele, target.prgele)
 end(acc)
        else subpass2(alltypes,big,core,small,count+1))
 
 

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

 

