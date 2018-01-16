Module printbitcodes

run printbitcodes test1

use bits

use fileio

use internalbc

use llvm

use oseq.codefreq

use seq.bit

use seq.block

use seq.boolean

use seq.codefreq

use seq.content

use seq.decodename

use seq.seq.int

use stdlib

Function test1 seq.word printBitCodes."test3.bc"

Function printBitCodes(file:seq.word)seq.word 
 let discard = initnames 
  let d = getbitfile.file 
  assert print.subseq(d, 1, 64)="66 67 192 222 33 12 0 0"report"incorrect magic"+ print.subseq(d, 1, 64)
  let m = block(subseq(d, 97, length.d), 3, MODULEBLOCK)
  let z = getinfo.m 
  let types = recs.getinfo(findblock(TYPEBLOCK, blocks.z)_1)
  let symbols = findblock(VALUESYMTABBLOCK, blocks.z)_1 
  let constants = findblock(CONSTANTSBLOCK, blocks.z)_1 
  let deflist = subseq(recs.z, 2, length.recs.z)
  let symlist = print3.symbols 
  let constlist = printconstant(recs.getinfo.constants, -1, length.deflist, 1, empty:seq.seq.word)
  {"let TYPES = ["+ printtypes.types +"]"+"&br let DEFLIST = ["+ label("&br", symlist, @(+, print.MODULEBLOCK, empty:seq.seq.word, deflist), 1,"")+"]"+"&br let CONSTANTS = ["+ @(seperator.",", identity,"", constlist)+"]"+"&br let bodies = ["+ printfuncs(length.deflist + length.constlist, types, deflist, symlist, 1, findblock(FUNCTIONBLOCK, blocks.z), 1,"")+"]"}

function printtypes(r:seq.seq.int)seq.word 
 label("&br", ["X"]+ printtypes(r, 2, empty:seq.seq.word), @(+, print.TYPEBLOCK, empty:seq.seq.word, r), 1,"")

label("&br", print3.symbols, print3.deflist, 1, 0)

function printfuncs(offset:int, types:seq.seq.int, deflist:seq.seq.int, symlist:seq.seq.word, i:int, defs:seq.block, j:int, result:seq.word)seq.word 
 if i > length.deflist 
  then result + if j < length.defs then"&br + extra bodies"else""
  else if deflist_i_1 = MODULECODEFUNCTION ∧ deflist_i_4 = 0 
  then let nopara = length(types_(deflist_i_2 + 2)) - 3 
   let a =(if length.result = 0 then""else",")+"&br //"+ symlist_i +"nopara:"+ toword.nopara +"//"+ if j > length.defs 
    then"missing body"
    else // print2(defs_j)// yy(recs.getinfo(defs_j), 1, offset + nopara + 1,"", offset)
   printfuncs(offset, types, deflist, symlist, i + 1, defs, j + 1, result + a)
  else printfuncs(offset, types, deflist, symlist, i + 1, defs, j, result)

function print2(a:block)seq.word 
 let r = recs.getinfo.a 
  @(seperator.",", print.blockid.a,"", r)

function print3(a:block)seq.seq.word 
 let r = recs.getinfo.a 
  @(+, print.blockid.a, empty:seq.seq.word, r)

function label(prefix:seq.word, labels:seq.seq.word, items:seq.seq.word, i:int, result:seq.word)seq.word 
 if i > length.items 
  then result 
  else let a = if i > length.labels 
   then prefix + items_i 
   else(if i > 1 then","else"")+ prefix +"//"+ labels_i +"//"+ items_i 
  label(prefix, labels, items, i + 1, result + a)

function printconstant(s:seq.seq.int, lasttype:int, number:int, i:int, result:seq.seq.word)seq.seq.word 
 if i > length.s 
  then result 
  else let a = s_i 
  if a_1 = CONSTSETTYPE 
  then printconstant(s, a_2, number, i + 1, result)
  else let b ="&br //"+ toword.number +"// C("+ toword.lasttype +","+ print(CONSTANTSBLOCK, a)+")"
  printconstant(s, lasttype, number + 1, i + 1, result + b)

function print(blockid:int, a:seq.int)seq.word 
 if blockid = VALUESYMTABBLOCK 
  then [ toword(a_2), encodeword.subseq(a, 3, length.a)]
  else @(xx.blockid, identity,"", a)+"]"

function xx(blockid:int, a:seq.word, v:int)seq.word 
 a + if length.a = 0 
  then(if blockid in [ TYPEBLOCK, MODULEBLOCK, CONSTANTSBLOCK]
   then"["
   else"&br [")+ lookup(blockid, v)
  else","+ toword.v

function print(a:seq.bit)seq.word @(+, asbyte.a,"", arithseq(length.a / 8, 8, 1))

function asbyte(a:seq.bit, i:int)seq.word [ toword.toint.@(formval.a, identity, bits.0, arithseq(8, -1, i + 7))]

function formval(a:seq.bit, val:bits, i:int)bits val << 1 ∨ bits.toint(a_i)

type pp is record idx:int, val:int

function getvbr(a:seq.bit, idx:int, size:int)pp getvbr(a, size, bits.0, 0, idx, 0)

function getvbr(a:seq.bit, size:int, val:bits, nobits:int, idx:int, i:int)pp 
 let b = toint(a_(idx + i))
  if i = size - 1 
  then if b = 0 then pp(idx + size, toint.val)else getvbr(a, size, val, nobits, idx + size, 0)
  else getvbr(a, size, bits.b << nobits ∨ val, nobits + 1, idx, i + 1)

function align32(p:pp)pp 
 let m =(idx.p - 1)mod 32 
  if m = 0 then p else pp(idx.p + 32 - m, 0)

function filter(blockid:int, a:block)seq.block 
 if blockid = blockid.a then [ a]else empty:seq.block

function findblock(blockid:int, a:seq.block)seq.block @(+, filter.blockid, empty:seq.block, a)

type content is record recs:seq.seq.int, blocks:seq.block

type block is record bits:seq.bit, abbrevlen:int, blockid:int

function print(a:block)seq.word 
 {"abbrvlen:"+ toword.abbrevlen.a +"blockid:"+ toword.blockid.a +"len"+ toword.length.bits.a }

function getinfo(a:block)content 
 getinfo(bits.a, 0, empty:seq.int, 1, empty:seq.seq.int, empty:seq.block, abbrevlen.a, blockid.a)

function getinfo(b:seq.bit, noargs:int, r:seq.int, idx:int, recs:seq.seq.int, blocks:seq.block, abbrvlen:int, blockid:int)content 
 if length.r > 0 
  then // working on record // 
   if noargs = 0 
   then getinfo(b, 0, empty:seq.int, idx, recs + r, blocks, abbrvlen, blockid)
   else let next = getvbr(b, idx, 6)
   getinfo(b, noargs - 1, r + val.next, idx.next, recs, blocks, abbrvlen, blockid)
  else let t = getvbr(b, abbrvlen, bits.0, 0, idx, 0)
  if val.t = 3 
  then // record // 
   let inst = getvbr(b, idx.t, 6)
   let args = getvbr(b, idx.inst, 6)
   getinfo(b, val.args, [ val.inst], idx.args, recs, blocks, abbrvlen, blockid)
  else if val.t = 1 
  then // block // 
   let newblockid = getvbr(b, idx.t, 8)
   let abbrlen = getvbr(b, idx.newblockid, 4)
   let alg = align32.abbrlen 
   let len = getvbr(b, idx.alg, 32)
   let end = idx.len + val.len * 32 
   getinfo(b, 0, empty:seq.int, end, recs, blocks + block(subseq(b, idx.len, end - 1), val.abbrlen, val.newblockid), abbrvlen, blockid)
  else content(recs, blocks)

type decodename is record block:int, code:int, name:seq.word

type nameencoding is encoding decodename

function =(a:decodename, b:decodename)boolean block.a = block.b ∧ code.a = code.b

function hash(a:decodename)int {(block.a + 2)*(code.a + 2)}

Function lookup(block:int, code:int)seq.word 
 let a = encode(decodename(block, code,"// unknown //"+ toword.code), nameencoding)
  name.decode(a, nameencoding)

function I(block:int, code:int, name:seq.word)int 
 let a = encode(decodename(block, code, name), nameencoding)
  0

Function initnames int 
 let z = [ I(MODULEBLOCK, 1,"Version"), 
  I(MODULEBLOCK, MODULECODEGLOBALVAR,"MODULECODEGLOBALVAR"), 
  I(MODULEBLOCK, MODULECODEFUNCTION,"MODULECODEFUNCTION"), 
  I(TYPEBLOCK, TYPEARRAY,"TYPEARRAY"), 
  I(TYPEBLOCK, TYPEPOINTER,"TYPEPOINTER"), 
  I(TYPEBLOCK, TYPEINTEGER,"TYPEINTEGER"), 
  I(TYPEBLOCK, TYPEFUNCTION,"TYPEFUNCTION"), 
  I(TYPEBLOCK, TYPEVOID,"TYPEVOID"), 
  I(TYPEBLOCK, OPAQUE,"OPAQUE"), 
  I(TYPEBLOCK, 1,"NumEle"), 
  I(FUNCTIONBLOCK, INSTBLOCK,"BLOCKCOUNT"), 
  I(FUNCTIONBLOCK, INSTNOPARA,"NO PARAMETERS"), 
  I(FUNCTIONBLOCK, INSTBR,"BR"), 
  I(FUNCTIONBLOCK, INSTRET,"RET"), 
  I(FUNCTIONBLOCK, INSTCAST,"CAST"), 
  I(FUNCTIONBLOCK, INSTCMP2,"CMP2"), 
  I(FUNCTIONBLOCK, INSTCALL,"CALL"), 
  I(FUNCTIONBLOCK, INSTGEP,"GEP"), 
  I(FUNCTIONBLOCK, INSTPHI,"PHI"), 
  I(FUNCTIONBLOCK, INSTBINOP,"BINOP"), 
  I(FUNCTIONBLOCK, INSTLOAD,"LOAD"), 
  I(FUNCTIONBLOCK, INSTSTORE,"STORE"), 
  I(FUNCTIONBLOCK, INSTALLOCA,"ALLOCA"), 
  I(CONSTANTSBLOCK, CONSTSETTYPE,"CONSTSETTYPE"), 
  I(CONSTANTSBLOCK, CONSTGEP,"CONSTGEP"), 
  I(CONSTANTSBLOCK, CONSTDATA,"CONSTDATA"), 
  I(CONSTANTSBLOCK, AGGREGATE,"AGGREGATE"), 
  I(CONSTANTSBLOCK, CSTRING,"CSTRING"), 
  I(CONSTANTSBLOCK, CONSTNULL,"CONSTNULL"), 
  I(CONSTANTSBLOCK, CONSTCECAST,"CONSTCECAST"), 
  I(CONSTANTSBLOCK, CONSTINTEGER,"CONSTINTEGER"), 
  I(VALUESYMTABBLOCK, ENTRY,"ENTRY")]
  3

function printtypes(t:seq.seq.int, i:int, result:seq.seq.word)seq.seq.word 
 if i > length.t 
  then @(+, number.result, empty:seq.seq.word, arithseq(length.result, 1, 1))
  else let a = t_i 
  let tp = a_1 
  let str = if tp = TYPEINTEGER 
   then [ merge("i"+ toword(a_2))]
   else if tp = TYPEARRAY 
   then"["+ toword(a_2)+"x"+ lookuptype(result, a_3)+"]"
   else if tp = TYPEPOINTER 
   then lookuptype(result, a_2)+"*"
   else if tp = TYPEFUNCTION 
   then"("+ @(seperator.",", lookuptype.result,"", subseq(a, 3, length.a))+")"
   else if tp = TYPEVOID then"VOID"else"?"
  printtypes(t, i + 1, result + str)

function lookuptype(s:seq.seq.word, i:int)seq.word s_(i + 1)

function number(s:seq.seq.word, i:int)seq.word [ toword(i - 1)]+":"+ s_i

function yy(s:seq.seq.int, i:int, slot:int, result:seq.word, offset:int)seq.word 
 if i > length.s 
  then result 
  else let d = s_i 
  let tp = d_1 
  let relocmask = if tp in [ INSTBINOP, INSTSTORE, INSTCMP2]
   then [ false, true, true, false, false]
   else if tp in [ INSTLOAD, INSTRET, INSTCAST]
   then [ false, true, false, false, false]
   else if tp in [ INSTBR, INSTALLOCA]
   then [ false, false, false, true, false]
   else if tp = INSTCALL 
   then [ false, false, false, false]+ constantseq(length.d - 4, true)
   else if tp = INSTGEP 
   then [ false, false, false]+ constantseq(length.d - 3, true)
   else if tp = INSTPHI 
   then if length.d < 8 then [ false, false, true, false, true, false, true, false, true]else [ false]+ big(length.d / 2)
   else if tp = 1 
   then [ false, false]
   else assert false report"unknown"+ lookup(FUNCTIONBLOCK, d_1)
   empty:seq.boolean 
  let slotinc = if tp in [ INSTLOAD, INSTALLOCA, INSTCALL, INSTGEP, INSTCAST, INSTCMP2, INSTBINOP, INSTPHI]
   then 1 
   else 0 
  yy(s, i + 1, slot + slotinc, result +(if length.result = 0 then"&br"else"+ &br")+ lookup(FUNCTIONBLOCK, d_1)+"("+ toword(slot - offset)+ yy(relocmask, d, length.d, offset, slot)+")", offset)

function big(i:int)seq.boolean 
 if i < 4 
  then [ false, true, false, true, false, true, false, true]
  else let t = big(i / 2)
  t + t

function yy(relocmask:seq.boolean, s:seq.int, i:int, offset:int, slot:int)seq.word 
 {(if i < 3 then""else yy(relocmask, s, i - 1, offset, slot))+","+ if relocmask_i 
  then let arg = s_i 
   {"("+ toword.(if slot - arg > offset then offset + arg - slot else slot - arg - 1)+")"} 
  else [ toword(s_i)]}

type codefreq is record count:int, w:int

function =(a:codefreq, b:codefreq)boolean false

function ?(a:codefreq, b:codefreq)ordering count.a ? count.b

function count(s:seq.codefreq, w:int)seq.codefreq replace(s, w, codefreq(count(s_w)+ 1, w))

function print(block:int, p:codefreq)seq.word 
 if count.p = 0 
  then empty:seq.word 
  else"&br the code"+ lookup(block, w.p)+"occurs"+ toword.count.p +"times."+ EOL

function removelowcount(mincount:int, p:codefreq)seq.codefreq 
 if count.p < mincount then empty:seq.codefreq else [ p]

function codefreq(mincount:int, a:seq.seq.int)seq.codefreq 
 sort.@(+, removelowcount.mincount, empty:seq.codefreq, @(count, identity, dseq.codefreq(0, 1), a))

function count(s:seq.codefreq, w:seq.int)seq.codefreq count(s, w_1)

Function test2 seq.word stats."test2.bc"

Function stats(file:seq.word)seq.word 
 let discard = initnames 
  let d = getbitfile.file 
  assert print.subseq(d, 1, 64)="66 67 192 222 33 12 0 0"report"incorrect magic"+ print.subseq(d, 1, 64)
  let m = block(subseq(d, 97, length.d), 3, MODULEBLOCK)
  let z = getinfo.m 
  let insts = @(+, recs, empty:seq.seq.int, @(+, getinfo, empty:seq.content, findblock(FUNCTIONBLOCK, blocks.z)))
  let constants = findblock(CONSTANTSBLOCK, blocks.z)_1 
  @(+, print.CONSTANTSBLOCK,"", codefreq(0, recs.getinfo.constants))+ @(+, print.FUNCTIONBLOCK,"", codefreq(0, insts))

