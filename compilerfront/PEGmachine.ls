Module PEGmachine

use PEGrules

use seq.seq.int

use standard

use otherseq.seq.word

use stack.seq.word

type machine is constants:seq.seq.word, actions:seq.seq.int

Export type:machine

function otherinst seq.word "/e /length"

function /e int-1

function /length int-2

Function postprocess(m:machine, old:seq.word, new:seq.word) machine
if isempty.old then
m
else
 assert n.old = n.new report "PEG:^(dq.old) must be same length as^(dq.new)"
 for constants = empty:seq.seq.word, e ∈ constants.m
 do constants + [wordReplace(e, old, new)],
 machine(constants, actions.m)

Function runMachine(
 actno:int
 , actions:machine
 , strings:seq.seq.word
 , t:seq.word
) seq.word
for stk = empty:stack.seq.word, inst ∈ actno_actions.actions
do
 if inst > 0 then
 push(stk, inst_constants.actions)
 else if inst < -n.otherinst then
 push(stk, (-n.otherinst - inst)_strings)
 else if inst = /e then
 push(stk, "")
 else
  assert inst = /length report "???"
  for acc = "", e ∈ toseq.stk << 1 do acc + e,
  push(push(empty:stack.seq.word, 1_toseq.stk), "~length^(n.acc)^(acc)")
for acc = "", e ∈ toseq.stk do acc + e,
acc

Function makeInterperter(gin:seq.pegrule) machine
for acc0 = machine(empty:seq.seq.word, [empty:seq.int]), r ∈ gin
do
 if kind.r ∈ "!" then
 acc0
 else
  for acc = acc0, part ∈ parts.r
  do
   let subs = otherinst + NonTerminals(part, gin)
   for str = "", consts = constants.acc, actions = empty:seq.int, w ∈ replacement.part
   do
    let i = findindex(subs, w),
     if i > n.subs then
     next(str + w, consts, actions)
     else if isempty.str then
     next(str, consts, actions + [-i])
     else
      let j = findindex(consts, str),
       if j > n.consts then
       next("", consts + str, actions + [n.consts + 1,-i])
       else next("", consts + str, actions + [j,-i])
   ,
    if isempty.str then
    machine(consts, actions.acc + actions)
    else
     let k = findindex(consts, str),
      if k > n.consts then
      machine(consts + str, actions.acc + [actions + [n.consts + 1]])
      else machine(consts, actions.acc + [actions + k])
  ,
  acc
,
acc0 