Module markup.T

use UTF8

use seq1.char

use classinfo

use seq1.classinfo

use set.classinfo

use format1a

use seq1.mark

use stack.mark

use standard

use seq1.seq.word

use stack.seq.word

use seq1.word

unbound dawsextensions:T(op:word, argstk:stack.seq.word) stack.seq.word
{return empty:stack.seq.word if not defined}

/function showZ:T(out:seq.word)seq.word for acc ="", w ∈ out do acc+encodeword(decodeword.w+char1."Z"), acc

Function txt2html:T(z:seq.seq.word, classes:seq.classinfo, headertext:seq.word) UTF8
let xhtml = subseq(headertext, 1, 2) ∉ ["<!doctype html>", "<!doctype html"],
textFormat.headertext + HTMLformat1a.txt2html:T(z, classes, xhtml)

Function txt2html:T(z:seq.seq.word, classes:seq.classinfo, xhtml:boolean) seq.word
{covert paragraph to html}
let replacements = asset.classes
let gdefatt = lookupkey(replacements, "/global$defs" sub 1)
let globaldefs = if isempty.gdefatt then "" else def.gdefatt sub 1
let pdef = def.lookupkey(replacements, "/p" sub 1) sub 1
for acc0 = "", mark0 = push(empty:stack.mark, mark("block" sub 1, 0)), pno = 1, p ∈ z
do
 for last = "?" sub 1, skip = false, defines = "", marks = mark0, acc = acc0, e ∈ p + "/p"
 do
  if e = escapeformat then next(e, not.skip, defines, marks, acc + e)
  else if skip then next(e, skip, defines, marks, acc + e)
  else if last ∈ "block" ∧ e ∈ "/br" then next(e, skip, defines, marks, acc)
  else if e ∈ "//" then next(e, skip, defines, push(marks, n.acc), acc)
  else if e ∈ "/p" then
   let place = place.top.marks,
   if n.acc = place then next(e, skip, defines, marks, acc)
   else
    let content = subseq(acc, place + 1, n.acc)
    let newacc =
     subseq(acc, 1, place)
     + evaldef:T(defines + pdef, content, xhtml, subseq(z, 1, pno))
     + encodeword.[char.10],
    let newmarks = if kind.top.marks ∈ "block" then pop.marks else marks,
    next(e, skip, defines, push(newmarks, mark("block" sub 1, n.newacc)), newacc)
  else
   let r = lookupkey(replacements, e),
   if isempty.r then next(e, skip, defines, marks, acc + e)
   else
    let att = r sub 1
    let basedon = baseon.att,
    if isnamedmark.att ∧ key.att = tag.att then {marks beginning of tag}next(e, skip, defines, push(marks, mark(basedon, n.acc)), acc)
    else if ismark.att ∨ isdefine.att then
     let nomark = isempty.marks ∨ kind.top.marks ∉ "mark"
     let lastplace = if nomark then n.acc - 1 else place.top.marks
     let smallacc = subseq(acc, 1, lastplace)
     let content = subseq(acc, lastplace + 1, n.acc)
     let combinedDef = defines + def.att + globaldefs
     let new =
      (if isdefine.att then "" else smallacc)
      + evaldef:T(combinedDef, content, xhtml, subseq(z, 1, pno)),
     let stk2 = if nomark then marks else pop.marks,
     if isdefine.att then next(e, skip, defines + new, stk2, smallacc)
     else next(e, skip, "", stk2, new)
    else
     for acc1 = acc, ee ∈ [1]
     while basedon ∈ "/div" ∧ kind.top.marks ∈ "block" ∧ place.top.marks < n.acc1
     do
      let content = subseq(acc1, place.top.marks + 1, n.acc1),
      acc1 >> n.content + "/!< p /!>" + content
     let marks1 =
      if basedon ∈ "/caption" ∧ kind.top.marks ∈ "mark" then pop.marks
      else if basedon ∈ {???? should somehow make a group of these eles}"/div /li /svg /g /defs /td"
      ∧ kind.top.marks ∈ "block" then pop.marks
      else if basedon ∈ "/ol /ul" then
       for marks1 = marks while kind.top.marks1 ∈ "block /li" ∧ place.top.marks1 = n.acc1 do pop.marks1,
       marks1
      else if basedon ∈ "/td" ∧ kind.top.marks ∈ "/th" then push(pop.marks, mark(basedon, place.top.marks))
      else if basedon ∈ "/tr" ∧ kind.top.marks ∈ "/td /th" then pop.marks
      else if basedon ∈ "/table" ∧ place.top.marks = n.acc1 then
       let stkt = if kind.top.marks ∈ "block" then pop.marks else marks,
       if kind.top.stkt ∈ "/tr" then pop.stkt else stkt
      else marks
     let lastplace =
      if basedon ∈ "/head" then 0 else if isnocontent.att then n.acc1 else place.top.marks1
     let smallacc = subseq(acc1, 1, lastplace)
     let content = subseq(acc1, lastplace + 1, n.acc1)
     let combinedDef = defines + def.att + globaldefs
     let new =
      (if isdefine.att then "" else smallacc)
      + evaldef:T(combinedDef, content, xhtml, subseq(z, 1, pno))
     let stk7 =
      if basedon = kind.top.marks1 then pop.marks1
      else if basedon ∈ "/td" ∧ kind.top.marks1 ∈ "/th" then pop.marks
      else if basedon ∈ "/ol" ∧ kind.top.marks1 ∈ "/ul" then pop.marks
      else if basedon ∈ "/ul" ∧ kind.top.marks1 ∈ "/ol" then pop.marks
      else if basedon ∈ "/caption" ∧ kind.top.marks1 ∈ "mark" then pop.marks
      else marks1,
     let stk2 =
      if basedon ∈ "/tr /td /th /li" then push(stk7, mark(basedon, n.new))
      else if basedon ∈ "/br" then marks1
      else if basedon ∈ "/caption" then push(stk7, mark("/tr" sub 1, n.new))
      else
       {if not.isempty.stk7 ∧ kind.top.stk7 ∈"/div /td /th"then push(stk7, mark("block"sub 1, n.new))else}
       let stk5 = if not.isempty.stk7 ∧ kind.top.stk7 ∈ "block" then pop.stk7 else stk7,
       push(stk5, mark("block" sub 1, n.new)),
     next(e, skip, "", stk2, new),
 next(acc, marks, pno + 1),
acc0

function evaldef:T(
defs:seq.word
, content:seq.word
, xhtml:boolean
, raw:seq.seq.word
) seq.word
let alldefs = getDefines.defs
let rr = parseBB2.extractdef(alldefs, "tohtml")
for acc = "", e ∈ rr
do
 acc
 + if name.e = "no eval" then value.e
 else
  {now evaluate exp and assign result to value}
  for stk = empty:stack.seq.word, state = 0, ele ∈ value.e
  do
   if ele ∈ "'" then next(stk, 1)
   else if ele ∈ "/nsp /sp" ∨ state = 1 then next(push(stk, [ele]), 0)
   else if ele ∈ "content" then next(push(stk, content), 0)
   else if ele ∈ "colon" then next(push(stk, ": "), 0)
   else if ele ∈ "/post /pre" then
    {designed to add directory and extension to file names}
    assert n.toseq.stk > 1 report "XXX B"
    let second = top.stk
    let first = top.pop.stk,
    let val =
     if ele ∈ "pre" then
      if isempty.second ∨ first << (n.first - n.second) = second ∨ second sub 1 ∈ first then first
      else first + second
     else
      {post}
      if isempty.first then second
      else if first << (n.first - n.second) = second then first
      else first + second,
    next(push(pop(stk, 2), val), state)
   else if ele ∈ "/raw" then
    let endtag = merge("/" + last.last.raw)
    for txt = "", quit = false, p0 ∈ reverse.raw
    while not.quit
    do
     let p5 =
      if not.isempty.txt then p0
      else
       {???? needto look up p sub p.n-1 to find out if it is based on"/p"}
       let aa = if subseq(p0, n.p0 - 1, n.p0 - 1) = "/p" then 2 else 1
       {???? bug in formating when aa is removed}
       p0 >> aa
     for end = false, p1 = "", w ∈ p5
     do
      if w = endtag then next(true, "")
      else if w ∈ "/br" then next(end, p1 + "/ /nsp br" + w)
      else if w ∈ "/p" then next(end, p1 + "/ /nsp p")
      else next(end, p1 + w),
     next(p1 + "/br /br" + txt, end),
    next(push(stk, txt >> 2), state)
   else
    let result = dawsextensions:T(ele, stk),
    if not.isempty.result then next(result, state)
    else
     let value = extractdef(alldefs, [ele])
     let newstk = push(stk, value),
     next(newstk, state)
  let value = %.toseq.stk,
  if isempty.name.e then value else attribute(value, name.e),
acc 