Module printbitcodes

use UTF8

use bitcodesupport

use bits

use llvmconstants

use slotdesc

use standard

use textio

use format

use words

use seq.block

use encoding.blockabbr

use seq.blockabbr

use otherseq.boolean

use seq.boolean

use seq.char

use otherseq.codefreq

use seq.codefreq

use sparseseq.codefreq

use seq.constop

use seq.content

use seq.instop

use seq.int

use seq.slotdesc

use otherseq.word

use seq.word

use set.word

use sparseseq.word

use seq.seq.int

stats (" tools.bc")

use file

use seq.file

use otherseq.byte

function getcontent(in:file) content
let d = SBIT.data.in
let start = 
 if %.subseq(sbit.d, 1, 4) = "222 192 23 11" then
  val.getfixed(d, 65, 32) * 8 + 1
 else
  1
let magic = subseq(sbit.d, 1, 4)
assert magic = [tobyte.66, tobyte.67, tobyte.192, tobyte.222]
report
 "incorrect magic $(subseq(sbit.d, 1, 4 * 101)) starting at" + toword.start
 + toword.val.getfixed(d, 65, 32)
let tX = getfixed(d, start + 32, 2)
let newblockidX = getvbr(d, idx.tX, 8)
{assert false report [toword.val.tX, toword.val.newblockidX]}
let start2 = 
 if val.newblockidX = 13 then
  let len = getvbr(d, idx.align32.newblockidX, 32),
  idx.len + 32 * val.len
 else
  start + 32
let t = getvbr(d, 2, bits.0, 0, start2, 0)
let newblockid = getvbr(d, idx.t, 8)
let newabbrlen = getvbr(d, idx.newblockid, 4)
let len = getvbr(d, idx.align32.newabbrlen, 32)
assert val.t = 1 ∧ val.newblockid = toint.MODULE
report
 "incorrect format" + toword.val.t + toword.val.newblockid
 + toword.val.getvbr(d, idx.newabbrlen, 4)
 + toword.val.getvbr(d, idx.len, 4)
 + "/br"
{first block}
let m = block(d, idx.len, val.len, val.newabbrlen, toint.MODULE),
getinfoB.m

Function bitcodestats(input:seq.file, o:seq.word) seq.file
{Print frequency of useage in bitcode file}
let z = getcontent.first.input
let insts = 
 for acc = empty:seq.seq.int
  , @e ∈ for acc = empty:seq.content, @e ∈ findsubblock(toint.FUNCTIONBLK, blocks.z) do
   acc + getinfoB.@e
  /do acc
 do
  acc + recs.@e
 /do acc
let constants = 
 for acc = empty:seq.seq.int
  , @e ∈ for acc = empty:seq.content, @e ∈ findsubblock(toint.FUNCTIONBLK, blocks.z) do
   acc + getinfoB.@e
  /do acc
 do
  acc + recs.@e
 /do acc
let str1 = 
 for acc = "", @e ∈ codefreq(0, constants) do acc + print(toint.CONSTANTS, @e) /do acc /for
 + for acc = "", @e ∈ codefreq(0, insts) do acc + print(toint.FUNCTIONBLK, @e) /do acc
,
[file(filename.o, str1)]

Function printbitcodes(input:seq.file, o:seq.word, bitcode:boolean, check:boolean, objects:boolean
 , llvm:boolean) seq.file
{Decode a a bitcode file generated by the compiler into a more readable format.
 /br flags
 /br objects--decode reference to objects. 
 /br bitcode--includes code to generate module that can be compile with runcode.ls to regenerate the
 .bc file. 
 /br llvm--changes the format of the ouput to be more like the llvm.ll format. ???? not finished
 /br check--includes the orignial bc records in the output so any differences between the original
 and regenerated record can be detected. }
let z = getcontent.first.input
{let z2 = getinfo.(blocks.z)_5 @ (seperator."
 /br", printrecord.toint.MODULE,"", recs.z)}
let functionblocks = findsubblock(toint.FUNCTIONBLK, blocks.z)
let typeblock = 
 if blockid.(blocks.z)_2 = toint.TYPES then
  2
 else
  assert blockid.(blocks.z)_1 = toint.TYPES report "Expected TYPE Table as first block",
  1
let types = 
 for acc = empty:seq.seq.int, @e ∈ recs.getinfoB.(blocks.z)_typeblock do
  acc + removeabbr.@e
 /do acc
let q1 = 
 for acc = empty:seq.seq.word, @e ∈ arithseq(length.types - 1, 1, 0) do
  acc + printtype(types, @e, llvm)
 /do acc
assert blockid.last.blocks.z = toint.VALUESYMTABLE report "EXPECTED SYMBOL Table as last block"
let symbols = recs.getinfoB.last.blocks.z
let names = 
 for acc = sparseseq."undefinedname"_1, @e ∈ symbols do processsymentry(acc, @e) /do acc
let slots2 = slotorder2(z, 4, empty:seq.slotdesc)
let checkslots = number.check(slots2, q1)
assert "ERROR"_1 ∉ checkslots
report "check slot error (search for ERROR) /br" + number.q1 + checkslots
let constanddefs = descslot(check, objects, slots2, names, q1)
let ttt = for acc = "", e ∈ arithseq(length.q1, 1, 0) do acc + toword.e /do acc
let labels = for acc = empty:seq.seq.word, e ∈ ttt do acc + ("" + e) /do acc
let bodies = printbodies(functionblocks, slots2, constanddefs, q1, check, llvm) >> 3
let str1 = 
 if bitcode then
  "Module data
   /p use standard
   /p use runcode
   /p use seq.track
   /p use bitcodesupport
   /p use llvm
   /p use seq.llvmtype
   /p use seq.slot
   /p use llvmconstants
   /p use seq.seq.int
   /p use seq.seq.seq.int
   /p use internalbc
   /p use file
   /p use seq.file
   /p Function test2 (input:seq.file, o:seq.word) seq.file
   /br let tobepatched = typ.array (-2, i64)
   /br let discard = subseq (inittypes, 3, length.inittypes)
   /br let discard1 = initslots
   /br let a = for acc = empty:seq.seq.seq.int, e /in bodies do acc+finish.e /do acc /for
   /br let bc = llvm ([
   $(for acc = "", @e ∈ subseq(recs.getinfoB.(blocks.z)_typeblock, 2, 3) do
   acc + printrecord(TYPES, @e) + ","
  /do acc >> 1)
   ]+subseq (typerecords, 3, length.typerecords), a)
   /br, [file (filename (o), bc)]
   /p Function inittypes seq.llvmtype
   /br [$(number.q1)]
   /p Function initslots seq.slot
   /br [$(number.constanddefs)]
   /p Function bodies seq.track
   /br ["
  + bodies
  + "]"
 else
  obj2txt(objectfldslots(slots2, q1), constanddefs) + number.constanddefs + bodies
,
[file(filename.o, str1)]

function removeabbr(s:seq.int) seq.seq.int
if s_1 = -2 then empty:seq.seq.int else [s]

type info is recs:seq.seq.int
 , offset:int
 , blocks:seq.int
 , consts:seq.seq.word
 , types:seq.seq.word
 , check:boolean
 , llvm:boolean

function printbodies(blocks:seq.block
 , slots:seq.slotdesc
 , consts:seq.seq.word
 , types:seq.seq.word
 , check:boolean
 , llvm:boolean) seq.word
let seperator = 
 if llvm then "/p" else "/br, /br"
,
for result = empty:seq.word, codeblock = 1, slotno = 1, sl ∈ slots do
 let rec = rec.sl,
 if typ.sl ≠ -1 ∨ rec_1 ≠ toint.FUNCTIONDEC ∨ {external function} rec_4 = 1 then
  next(result, codeblock, slotno + 1)
 else
  {MODULECODEFUNCTION}
  let typ = types_(rec_2 + 1)
  let nopara = for acc = 0, e ∈ typ do if e ∈ "," then acc + 1 else acc /do acc
  let offset = length.consts - 1
  let inst = recs.getinfoB.blocks_codeblock
  let blocklabels = findblocks(inst, 1, nopara + 1, [nopara])
  let newinfo = info(inst, offset, blocklabels, consts, types, check, llvm)
  let b1 = printfuncbody(newinfo, offset + nopara, llvm)
  let b = 
   for acc = "", @e ∈ b1 do acc + @e + "+/br" /do acc >> 2
  ,
  next(
   result + for acc = "{", @e ∈ blocklabels do acc + toword.@e /do acc /for + "}"
   + "functionbody ("
   + lookupconst(consts, slotno - 1)
   + ","
   + toword.offset
   + ","
   + toword.nopara
   + ") /br+"
   + b
   + seperator
   , codeblock + 1
   , slotno + 1)
/do result

function printfuncbody(info:info, slotP:int, llvm:boolean) seq.seq.word
for slot = slotP, result = empty:seq.seq.word, inblock = 1, d ∈ recs.info do
 let tp = instop.d_1,
 if tp = instop.1 then
  {skip BLOCKCOUNT} next(slot, result, inblock)
 else
  let slotinc = if tp ∈ [LOAD, ALLOCA, CALL, GEP, CAST, CMP2, BINOP, PHI] then 1 else 0
  let ll = toword(slot - offset.info + inblock)
  let reglabel = if slotinc = 1 then if llvm then [merge.["%"_1, ll]] else "r." + ll else ""
  let pattern = 
   if tp = BINOP then
    let op1 = relocate(info, slot, d_2)
    let op2 = relocate(info, slot, d_3),
    "binaryop ($(reglabel), $(decode.binaryop.d_4), $(op1), $(op2))"
   else if tp = CMP2 then
    let op1 = relocate(info, slot, d_2)
    let op2 = relocate(info, slot, d_3),
    "cmp2 ($(reglabel), $(decode.cmp2op.d_4), $(op1), $(op2))"
   else if tp = CAST then
    let op1 = relocate(info, slot, d_2),
    if llvm then
     "$(reglabel) = $(decode.castop.d_4), $(op1), $(typ(info, d_3))"
    else
     "cast ($(reglabel), $(decode.castop.d_4), $(op1), $(typ(info, d_3)))"
   else if tp ∈ [LOAD] then
    let op1 = relocate(info, slot, d_2),
    "load ($(reglabel), $(op1), $(typ(info, d_3)), $(decode.align.d_4))"
   else if tp = RET then
    if length.d = 1 then "ret" else "ret ($(relocate(info, slot, d_2)))"
   else if tp ∈ [STORE] then
    let op1 = relocate(info, slot, d_2)
    let op2 = relocate(info, slot, d_3),
    "store ($(op1), $(op2), $(decode.align.d_4))"
   else if tp = GEP then
    "getelementptr ($(reglabel), $((types.info)_(d_3 + 1)),
     $(for acc = "", @e ∈ subseq(d, 4, length.d) do
     acc + relocate(info, slot, @e) + ","
    /do acc >> 1)
     )"
   else if tp = CALL then
    let fconst = relocate(info, slot, d_5),
    if llvm then
     let tt = break(","_1, (types.info)_(d_4 + 1) >> 1)
     let args = 
      for acc = "", types = tt << 1, @e ∈ subseq(d, 6, length.d) do
       next(acc + first.types + relocate(info, slot, @e) + ",", types << 1)
      /do acc >> 1
     ,
     "$(reglabel) = call $(first.tt << 3) $(fconst) (
      $(if length.args = 0 then ")" else "$(args))")"
    else
     let args = 
      for acc = "", @e ∈ subseq(d, 6, length.d) do
       acc + relocate(info, slot, @e) + ","
      /do acc >> 1
     ,
     "call ($(reglabel), $((types.info)_(d_4 + 1)), $(fconst)
      $(if length.args = 0 then ")" else ", [$(args)])")"
   else if tp = PHI then
    "phi ($(reglabel), $((types.info)_(d_2 + 1)) $(phi2(info, slot, d, 3, "")))"
   else if tp = ALLOCA then
    "alloca ($(reglabel), $((types.info)_(d_2 + 1)), $((types.info)_(d_3 + 1)),
     $(relocate(info, slot, d_4)))"
   else
    empty:seq.word
  let inst = 
   if not.isempty.pattern then
    pattern
   else if tp = BR then
    {assert false report @ (+, toword," BLOCKS", blocks.info)}
    if length.d = 4 then
     let op1 = relocate(info, slot, d_4),
     if between(d_2, 1, length.blocks.info) ∧ between(d_3, 1, length.blocks.info) then
      "br ($(op1)," + toword.(blocks.info)_(d_2 + 1) + ","
      + toword.(blocks.info)_(d_3 + 1)
      + ")"
     else
      "branch problem"
    else if between(d_2, 1, length.blocks.info) then
     "br.
      $(if between(d_2, 1, length.blocks.info) then
      [toword.(blocks.info)_(d_2 + 1)]
     else
      "{" + toword.d_2 + "} 0" + "+/br label." + ll
     )
      "
    else
     "branch problem" + toword(d_2 + 1)
   else
    reglabel + decode.instop.d_1 + for acc = "", @e ∈ d do acc + toword.@e /do acc
  ,
  next(slot + slotinc
   , result + if check.info then inst + "+" + printrecord(FUNCTIONBLK, d) else inst
   , if tp = BR then inblock + 1 else inblock)
/do result

use otherseq.seq.word

function phi2(info:info, slot:int, d:seq.int, i:int, result:seq.word) seq.word
if i > length.d then
 result
else
 let blklab = toword.(blocks.info)_(d_(i + 1) + 1)
 let x = d_i
 let y = x / 2
 let arg = if x = 2 * y then y else-y
 let reg = relocate(info, slot, arg),
 phi2(info
  , slot
  , d
  , i + 2
  , result + if i > 3 then "+" else "," /if + reg + "/" + blklab)

function relocate(info:info, slot:int, arg:int) seq.word
let offset = offset.info,
if {" ll"_1 in format.info} true then
 if slot - arg ≥ offset then
  let x = 
   for target = slot - arg - offset, b ∈ blocks.info
   while target ≥ b
   do
    target + 1
   /do target
  ,
  if llvm.info then [merge.["%"_1, toword.x]] else "r.$(x)"
 else if between(slot - arg + 1, 1, length.consts.info) then
  let t = lookupconst(consts.info, slot - arg + 1),
  if length.t > 10 then "slot." + toword(slot - arg + 1) else t
 else
  "???" + toword(slot - arg + 1)
else
 "("
 + toword.if slot - arg ≥ offset then-(slot - arg - offset + 1) else slot - arg /if
 + ")"

function typ(info:info, arg:int) seq.word (types.info)_(arg + 1)

function findblocks(s:seq.seq.int, i:int, rslot:int, blocks:seq.int) seq.int
if i > length.s then
 blocks
else
 let tp = instop.s_i_1
 let newblocks = if tp = BR then blocks + (rslot + length.blocks - 1) else blocks
 let slotinc = if tp ∈ [LOAD, ALLOCA, CALL, GEP, CAST, CMP2, BINOP, PHI] then 1 else 0,
 findblocks(s, i + 1, rslot + slotinc, newblocks)

function slotorder2(z:content, j:int, result:seq.slotdesc) seq.slotdesc
{result has blockid added as first element of record}
if j > length.recs.z then
 result
else
 let i = (recs.z)_j,
 if i_1 = -2 then
  slotorder2(z, j + 1, result)
 else if i_1 ≠ -1 then
  {not a sub block}
  if i_1 ∈ [toint.FUNCTIONDEC, toint.GLOBALVAR] then
   slotorder2(z, j + 1, result + slotdesc(-1, i))
  else
   slotorder2(z, j + 1, result)
 else
  let blocks = blocks.z,
  if blockid.blocks_(i_3) = toint.CONSTANTS then
   let recs = recs.getinfoB.blocks_(i_3),
   slotorder2(z, j + 1, result + slotorder2(recs, 1,-1, empty:seq.slotdesc))
  else
   slotorder2(z, j + 1, result)

function slotorder2(recs:seq.seq.int, i:int, lasttype:int, result:seq.slotdesc) seq.slotdesc
if i > length.recs then
 result
else
 let a = recs_i,
 if a_1 = toint.SETTYPE then
  slotorder2(recs, i + 1, a_2, result)
 else
  slotorder2(recs, i + 1, lasttype, result + slotdesc(lasttype, a))

function processsymentry(t:seq.word, a:seq.int) seq.word
replaceS(t, a_2 + 1, [encodeword.tocharseq.subseq(a, 3, length.a)])

function label(prefix:seq.word, labels:seq.seq.word, items:seq.seq.word, i:int, result:seq.word) seq.word
if i > length.items then
 result
else
 let a = 
  if i > length.labels then
   prefix + items_i
  else if i > 1 then "," else "" /if + prefix + "{" + labels_i + "}" + items_i
 ,
 label(prefix, labels, items, i + 1, result + a)

function filter(blockid:int, a:block) seq.block
if blockid = blockid.a then [a] else empty:seq.block

function findsubblock(blockid:int, a:seq.block) seq.block
for acc = empty:seq.block, @e ∈ a do acc + filter(blockid, @e) /do acc

function print(a:block) seq.word
"abbrvlen:" + toword.abbrevlen.a + "blockid:" + decode.blockop.blockid.a + "len"
+ toword.len.a

type blockabbr is blockid:int, abbrs:seq.seq.int

function =(a:blockabbr, b:blockabbr) boolean blockid.a = blockid.b

function hash(a:blockabbr) int hash.blockid.a

function processabbr(a:seq.seq.int, i:int, blockid:int, list:seq.seq.int) int
if i > length.a then
 if isempty.list then
  1
 else
  let discard = encode.blockabbr(blockid, list),
  1
else if a_i_1 = SETBID then
 if isempty.list then
  processabbr(a, i + 1, a_i_2, list)
 else
  let discard = encode.blockabbr(blockid, list),
  processabbr(a, i + 1, a_i_2, empty:seq.seq.int)
else if a_i_1 = -2 then
 processabbr(a, i + 1, blockid, list + a_i)
else
 processabbr(a, i + 1, blockid, list)

type codefreq is count:int, w:int

function =(a:codefreq, b:codefreq) boolean false

function >1(a:codefreq, b:codefreq) ordering count.a >1 count.b

function count(s:seq.codefreq, w:int) seq.codefreq
replaceS(s, w, [codefreq(count.s_w + 1, w)])

function print(block:int, p:codefreq) seq.word
if count.p = 0 then
 empty:seq.word
else
 "/br the code $(printrecord(blockop.block, [w.p, 0])) occurs" + toword.count.p
 + "times. /br"

function removelowcount(mincount:int, p:codefreq) seq.codefreq
if count.p < mincount then empty:seq.codefreq else [p]

function codefreq(mincount:int, a:seq.seq.int) seq.codefreq
sort.for acc = empty:seq.codefreq
 , @e ∈ for acc = sparseseq.codefreq(0, 1), @e ∈ a do count(acc, @e) /do acc
do
 acc + removelowcount(mincount, @e)
/do acc

function count(s:seq.codefreq, w:seq.int) seq.codefreq count(s, w_1)

use llvm2 