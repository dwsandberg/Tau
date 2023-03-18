Module makeentry

use PEG

use standard

Function modEntry(src:seq.seq.word) seq.word
 let tbl = entrygrammar,
  for acc = "", lastmod = "?"_1, uses = empty:set.seq.word, p ∈ src
  do
   if subseq(p, 1, 1) = "Module" then
   next(acc, p_2, uses)
   else
    let t = apply(tbl, p),
     if isempty.t then
     next(acc, lastmod, uses)
     else
      let abstract = p_3 ∈ ":"
      let cmd = if abstract then [p_2] + ":callconfig" else [p_2],
      next(
       acc + "/br else if cmd /in $(dq.cmd) then $(cmd) (input $(xxxx.t))"
       , lastmod
       ,
        if abstract then
        uses + "use tools /p" + "use $(lastmod).callconfig
         /p"
        else uses + ("use" + lastmod + "/p")
      )
  /do
   if isempty.uses then
   ""
   else
    "Module entrypoint /p use standard
     /p use file
     /p use llvmcode
     /p use seq.file
     /p use bits
     /p use seq.byte
     /p use process.UTF8
     /p"
    + %.toseq.uses
    + "Export addbcwords (seq.byte) int /p Function entrypoint (args:UTF8) UTF8
     /br let p = process.entrypoint2 (args),
     /br if aborted.p then finishentry.[file ($(dq."error.html"), message.p)] else result.p
     /p function entrypoint2 (args0:UTF8) UTF8
     /br let args = towords.args0,
     /br let cmd = first.args,
     /br let input = getfiles.args
     /br finishentry.$(acc << 2)
     /br else empty:seq.file"

use set.seq.word

use otherseq.seq.word

use otherseq.word

function xxxx(a:seq.seq.word) seq.word
 for txt2 = "", p ∈ a << 1
 do
  let kind = p_2
  let name = dq.[first.p],
   txt2
   + 
    if kind ∈ "words" then
    ", extractValue (args, $(name))"
    else if kind ∈ "boolean" then
    ", first.$(name) ∈ extractValue (args, $(dq."flags"))"
    else if kind ∈ "files" then
    ""
    else ", ?"
 /do txt2

Function entrygrammar PEGtable
maketable."S Header {CompilerOptions ENTRYPOINT options A4 /action /e /1 /length /3 /br Header Function any (K P) TYPE /action /1 /4 //br /2 /3
 /br / Function any:T (K P) TYPE /action /1 /4 //br /2 /3
 /br * P, K /action /0 //br /1
 /br K A1:TYPE /action /1 /2
 /br * A1 !:any /action /1
 /br * A4 any /action
 /br TYPE boolean /action boolean
 /br / seq.word /action words
 /br / seq.file /action files
 /br * desc ! //br !
 /p ! /strong ! *> ! <* !} any /action /0 /1
 /br * options /strong any desc Discard <* block values *> /action /0 /1 /4 /2 /length / /strong any desc /action /0 /1 /2 /length / Discard2 /action /0
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
  if first.a ∈ "Fail" then
  empty:seq.seq.word
  else
   let divide = toint.a_2 + 2,
    for
     final = break(subseq(a, 3, divide), "/br", false)
     , acc = ""
     , count =-1
     , last = "?"_1
     , w ∈ a << divide + "X"
    do
     if count > 0 then
     next(final, acc + w, count - 1, w)
     else if count = 0 then
     next(merge(final, acc), "",-1, w)
     else if last ∈ "~length" then
     next(final, acc, toint.w, w)
     else next(final, acc, count, w)
    /do final

function merge(a:seq.seq.word, b:seq.word) seq.seq.word
 for acc = empty:seq.seq.word, x ∈ a
 do if first.x = first.b then acc + [subseq(x, 1, 2) + b << 1] else acc + x
 /do acc

 