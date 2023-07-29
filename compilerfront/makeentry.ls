Module makeentry

use PEG

use standard

use otherseq.word

use otherseq.seq.word

use set.seq.word

Function modEntry2(src:seq.seq.word) seq.seq.word
for acc = empty:seq.seq.word, paragraph = empty:seq.word, w ∈ modEntry.src
do
 if w ∈ "/p" then
 next(if isempty.paragraph then acc else acc + paragraph, "")
 else if w ∈ "/br" then
 next(acc, paragraph)
 else next(acc, paragraph + w)
,
acc << 1 + paragraph

Function modEntry(src:seq.seq.word) seq.word
let tbl = entrygrammar
for acc = "", lastmod = 1_"?", uses = empty:set.seq.word, p ∈ src
do
 if subseq(p, 1, 1) = "Module" then
 next(acc, 2_p, uses)
 else
  let t = apply(tbl, p),
   if isempty.t then
   next(acc, lastmod, uses)
   else
    let abstract = 3_p ∈ ":"
    let cmd = if abstract then [2_p] + ":callconfig" else [2_p]
    let cmdReturnType = 2_1_t
    assert cmdReturnType ∈ "files words"
    report "Expected return type of ENTRYPOINT to be seq.file or seq.word for:^(p)",
    next(
     let runcmd =
      if 2_1_t ∈ "files" then
      "^(cmd)^(buildCommandArgs.t)"
      else "[file (extractValue (args,^(dq."o")),^(cmd)^(buildCommandArgs.t))]"
     ,
     acc + "/br else if cmd /in^(dq.cmd) then^(runcmd)"
     , lastmod
     ,
      {???? figure out how to remove use tools}
      if abstract then
       uses
       + "use tools /p"
       + "use^(lastmod).callconfig
        /p"
      else uses + ("use" + lastmod + "/p")
    )
,
if isempty.uses then
""
else "Module entrypoint /p use standard
 /p use file
 /p use llvmcode
 /p use seq.file
 /p use bits
 /p use seq.byte
 /p use process.UTF8
 /p^(toseq.uses)
 /p Export addbcwords (seq.byte) int
 /p Function entrypoint (args:UTF8) UTF8
 /br let p = process.entrypoint2 (args),
 /br if aborted.p then finishentry.[file (^(dq."error.html"), message.p)] else result.p
 /p function entrypoint2 (args0:UTF8) UTF8
 /br let args = towords.args0,
 /br let cmd = 1_args,
 /br let input = getfiles.args
 /br finishentry.^(acc << 2)
 /br else assert false report^(dq."No command named;")+cmd empty:seq.file"

function buildCommandArgs(a:seq.seq.word) seq.word
for txt2 = "", p ∈ a << 1
do
 let kind = 2_p
 let name = dq.[1_p],
  txt2
  + 
   if kind ∈ "words" then
   ", extractValue (args,^(name))"
   else if kind ∈ "boolean" then
   ", extractFlag (args,^(name))"
   else if kind ∈ "files" then
   ", input"
   else ", ?"
,
if isempty.txt2 then "" else "(^(txt2 << 1))"

Function entrygrammar PEGtable
maketable."S Header {CompilerOptions ENTRYPOINT options A4 /action /e /1 /length /3 /br Header Function any (FP FP') Type /action /1 /4 //br /2 /3
 /br / Function any:T (FP FP') Type /action /1 /4 //br /2 /3
 /br / Function any Type /action /1 /2
 /br * FP', FP /action /0 //br /1
 /br FP A1:Type /action /1 /2
 /br * A1 !:any /action /1
 /br * A4 any /action
 /br Type boolean /action boolean
 /br / seq.word /action words
 /br / seq.file /action files
 /br * desc ! //br !
 /p ! /strong ! *> ! <* !} any /action /0 /1
 /br * options /strong any desc Discard <* block values *> /action /0 /1 /4 /2 /length
 /br / /strong any desc /action /0 /1 /2 /length / Discard2 /action /0
 /br * values /strong desc /action /0 /1 /length / Discard2 /action /0
 /br * Discard2 <* block N *> /action
 /br / Discard /action
 /br * Discard <* ! block N *> /action
 /br / ! /strong ! <* ! *> !} any /action
 /br * N <* N *> /action
 /br / ! <* ! *> !} any /action
 /br * CompilerOptions OPTION /action discard
 /br / PROFILE /action discard
 /br / NOINLINE /action discard"

Function apply(tbl:PEGtable, p:seq.word) seq.seq.word
let a = run2(tbl, p),
if 1_a ∈ "Fail" then
empty:seq.seq.word
else
 let divide = toint.2_a + 2
 for
  final = break(subseq(a, 3, divide), "/br", false)
  , acc = ""
  , count =-1
  , last = 1_"?"
  , w ∈ a << divide + "X"
 do
  if count > 0 then
  next(final, acc + w, count - 1, w)
  else if count = 0 then
  next(merge(final, acc), "",-1, w)
  else if last ∈ "~length" then
  next(final, acc, toint.w, w)
  else next(final, acc, count, w)
 ,
 final

function merge(a:seq.seq.word, b:seq.word) seq.seq.word
for acc = empty:seq.seq.word, x ∈ a
do if 1_x = 1_b then acc + [subseq(x, 1, 2) + b << 1] else acc + x,
acc 