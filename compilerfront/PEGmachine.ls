Module PEGmachine

use PEGrules

use UTF8

use seq.char

use seq.seq.int

use seq.pegpart

use seq.pegrule

use standard

use otherseq.seq.word

use stack.seq.word

Export type:PEGtable

Export entries(PEGtable) seq.tableEntry

type PEGtable is entries:seq.tableEntry, constants:seq.seq.word, actions:seq.seq.int

Function %(t:PEGtable) seq.word %table.entries.t

function otherinst seq.word "/e /length"

function /e int-1

function /length int-2

function postProcess(m:PEGtable, subs:seq.word) PEGtable
if isempty.subs then m
else
 for constants = empty:seq.seq.word, e ∈ constants.m
 do constants + [replaceWords(e, subs)],
 PEGtable(postprocess(entries.m, subs), constants, actions.m)

Function runMachine(
actno:int
, actions:PEGtable
, strings:seq.seq.word
, t:seq.word
) seq.word
for stk = empty:stack.seq.word, inst ∈ actno#actions.actions
do
 if inst > 0 then push(stk, inst#constants.actions)
 else if inst <-n.otherinst then push(stk, (-n.otherinst - inst)#strings)
 else if inst = /e then push(stk, "")
 else
  assert inst = /length report "internal runMachine error"
  for acc = "", e ∈ toseq.stk << 1 do acc + e,
  push(push(empty:stack.seq.word, 1#toseq.stk), "~length^(n.acc)^(acc)")
for acc = "", e ∈ toseq.stk do acc + e,
acc

function preprocess(replacement:seq.word) seq.word
for acc = "", w ∈ replacement
do
 if subseq(acc, n.acc - 1, n.acc) = "$." then acc >> 2 + merge("$." + w)
 else acc + w,
acc

Function maketable(gin:seq.pegrule, subs0:seq.word, addrecover:boolean) PEGtable
let tbl = makeTbl(gin, addrecover)
for acc0 = PEGtable(tbl, empty:seq.seq.word, [empty:seq.int]), r ∈ gin
do
 if kind.r ∈ "!" then acc0
 else
  for acc = acc0, part ∈ parts.r
  do
   for subs = otherinst, i ∈ arithseq(NTcount(part, gin) + 1, 1, 0)
   do subs + merge."$.^(i)"
   for str = "", consts = constants.acc, actions = empty:seq.int, w ∈ preprocess.replacement.part
   do
    let i = findindex(subs, w),
    if i > n.subs then next(str + w, consts, actions)
    else if isempty.str then next(str, consts, actions + [-i])
    else
     let j = findindex(consts, str),
     if j > n.consts then next("", consts + str, actions + [n.consts + 1,-i])
     else next("", consts + str, actions + [j,-i]),
   if isempty.str then PEGtable(tbl, consts, actions.acc + actions)
   else
    let k = findindex(consts, str),
    if k > n.consts then PEGtable(tbl, consts + str, actions.acc + [actions + [n.consts + 1]])
    else PEGtable(tbl, consts, actions.acc + [actions + k]),
  acc,
postProcess(acc0, subs0) 