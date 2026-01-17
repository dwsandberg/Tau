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

Function processTXT:T(
z:seq.seq.word
, replacements:seq.classinfo
, xhtml:boolean
, lang:seq.word
) UTF8
let p1 = z sub 1
for header = 0, idx = 1, w ∈ p1
do next(if w ∈ "/base /link /title" then idx else header, idx + 1)
let newz = [subseq(p1, 1, header) + "/head", p1 << header] + z << 1
let final = textFormat1a(if xhtml then "/tag </body></html>" else ""),
textFormat1a(
 if xhtml then "<?xml version =:(dq."1.0")encoding =:(dq."utf-8")?> <html xmlns =:(dq."http://www.w3.org/1999/xhtml")xmlns:epub =:(dq."http://www.idpf.org/2007/ops")>"
 else "<!doctype html> <html lang /nsp =:(dq.":(lang)")> <meta charset /nsp =:(dq."utf-8")>"
)
 + HTMLformat1a.txt2html:T(newz, asset.replacements, xhtml)
 + final

Function txt2html:T(z:seq.seq.word, replacements:set.classinfo, xhtml:boolean) seq.word
{covert paragraph to html}
let gdefatt = lookupkey(replacements, "/global$defs" sub 1)
let globaldefs = if isempty.gdefatt then "" else def.gdefatt sub 1
let pdef = def.lookupkey(replacements, "/p" sub 1) sub 1
for acc0 = "", mark0 = push(empty:stack.mark, mark("block" sub 1, 0)), p ∈ z
do
 assert place.top.mark0 = n.acc0 report "check23:(top.mark0):(n.acc0)"
 for last = "?" sub 1, skip = false, defines = "", marks = mark0, acc = acc0, e ∈ p
 do
  if e = escapeformat then next(e, not.skip, defines, marks, acc + escapeformat)
  else if skip then next(e, skip, defines, marks, acc + e)
  else if last ∈ "/block" ∧ e ∈ "/br" then next(e, skip, defines, marks, acc)
  else if e ∈ "//" then next(e, skip, defines, push(marks, n.acc), acc)
  else
   let r = lookupkey(replacements, e),
   if isempty.r then next(e, skip, defines, marks, acc + e)
   else
    let att = r sub 1
    let basedon = baseon.att,
    if isnamedmark.att ∧ key.att = tag.att then
     {marks beginning of tag}
     let newmarks = push(push(pop.marks, mark(basedon, n.acc)), top.marks),
     next(e, skip, defines, newmarks, acc)
    else
     let acc1 = acc
     let marks1 =
      if basedon ∈ "/li" ∧ kind.top.marks ∈ "block" then
       if n.toseq.marks = 1 then
        let new =
         push(push(pop.marks, mark("/ul" sub 1, place.top.marks)), mark("/li" sub 1, place.top.marks)),
        new
       else
        let mark2 = advance:T(pop.marks, mark("/li" sub 1, place.top.marks)),
        mark2
      else if basedon ∈ "/div" ∧ kind.top.marks ∈ "block" ∧ place.top.marks = n.acc1 then pop.marks
      else if basedon ∈ "/ol /ul" then
       let marks2 =
        if kind.top.marks ∈ "block" ∧ place.top.marks = n.acc1 then pop.marks else marks
       assert kind.top.marks2 ∈ "/li" report "problem 890:(%n.toseq.marks):(p)",
       {???? should do more than just popstack doesnot assign class or and end tag}
       pop.marks2
      else if basedon ∈ "/tr" ∧ kind.top.marks ∈ "/td" then pop.marks
      else if basedon ∈ "/table" ∧ kind.top.marks ∈ "/tr" then pop.marks
      else marks
     assert basedon ∉ "/div" ∨ kind.top.marks1 = basedon report ":(key.att)does not have matching start"
     assert basedon ∉ "/ul /ol" ∨ kind.top.marks1 ∈ "/ul /ol /div" report ":(key.att)does not have matching start:(%n.toseq.marks1)/p:(p)"
     let lastplace =
      if basedon ∈ "/head" then 0
      else if (ismark.att ∨ isdefine.att) ∧ kind.top.marks1 ∉ "mark" then n.acc1 - 1
      else place.top.marks1
     let smallacc = subseq(acc1, 1, lastplace)
     let content = subseq(acc1, lastplace + 1, n.acc1),
     let combinedDef = defines + def.att + globaldefs,
     if isdefine.att then
      let eval = evaldef:T("", combinedDef, content, replacements, xhtml)
      let stk2 = if kind.top.marks1 ∈ "mark" then pop.marks1 else marks1,
      next(e, skip, defines + eval, stk2, smallacc)
     else
      let new = evaldef:T(smallacc, combinedDef, content, replacements, xhtml)
      let stk2 =
       if basedon ∈ "/caption" then push(marks1, mark("/tr" sub 1, n.new))
       else if ismark.att then if kind.top.marks1 ∈ "mark" then pop.marks1 else marks1
       else if basedon ∈ "/br" then marks
       else if basedon ∈ "/tr" then advance:T(marks1, mark("/tr" sub 1, n.new))
       else if basedon ∈ "/td /th" then advance:T(marks1, mark("/td" sub 1, n.new))
       else if basedon ∈ "/div" then push(pop.marks1, mark("block" sub 1, n.new))
       else
        let stk3 = if kind.top.marks1 ∈ "block" then pop.marks1 else marks1,
        if basedon ∈ "/ol /ul" ∧ kind.top.stk3 ∈ "/ol /ul" then push(pop.stk3, mark("block" sub 1, n.new))
        else advance:T(marks1, mark("block" sub 1, n.new)),
      next(e, skip, "", stk2, new),
 let newacc = finishp:T(acc, marks, xhtml, replacements, defines + pdef),
 if newacc = acc then next(acc, marks)
 else next(newacc, push(pop.marks, mark("block" sub 1, n.newacc)))
{assert false report"Final"+esc.acc0}
acc0

function advance:T(stk:stack.mark, m:mark) stack.mark
push(if kind.m = kind.top.stk then pop.stk else stk, m)

function finishp:T(
acc:seq.word
, marks:stack.mark
, xhtml:boolean
, replacements:set.classinfo
, defs:seq.word
) seq.word
if n.acc = place.top.marks then acc
else
 let top = place.top.marks
 let content = subseq(acc, top + 1, n.acc),
 evaldef:T(subseq(acc, 1, top), defs, content, replacements, xhtml)

function evaldef:T(
smallacc:seq.word
, defs:seq.word
, content:seq.word
, replacements:set.classinfo
, xhtml:boolean
) seq.word
let evalstr = extractdef(defs, "output" sub 1)
for
 haveatt = ""
 , stk = empty:stack.seq.word
 , acc = smallacc
 , intag = false
 , e3 ∈ evalstr + "?"
do
 if e3 ∈ "=" then
  if isempty.stk then next(haveatt, push(stk, "bottom"), acc, intag)
  else if intag ∧ not.isempty.haveatt then next("", empty:stack.seq.word, acc + attribute(top.stk, haveatt sub 1), intag)
  else next(haveatt, empty:stack.seq.word, acc + top.stk, intag)
 else
  let info = lookuptag(replacements, e3),
  if not.isempty.info then
   if isendtag.info sub 1 then
    let new = if xhtml ∨ e3 ∉ "</p> </li>" then acc + "/tag" + e3 else acc,
    next(haveatt, stk, new, intag)
   else
    {assert e3 ∈"<titlex"report"here gg JKL:(e3):(intag)"+acc+"/p"+evalstr}
    let acc1 =
     if e3 ∈ "<sub <sup" then if last.acc ∈ "/tag" then acc + e3 else acc + "/tag" + e3
     else acc + "/sp /tag" + e3,
    next("", stk, acc1, true)
  else if e3 ∈ "> />" then
   let end = if xhtml ∧ e3 ∈ "/>" then "/tag /> /nsp" else "/tag > /nsp"
   let lastatt =
    if not.isempty.haveatt ∧ intag then acc + attribute(extractdef:T(defs, haveatt sub 1, content), haveatt sub 1)
    else acc,
   next("", stk, lastatt + end, false)
  else if not.isempty.stk then
   if e3 ∈ "/post /pre" then
    assert n.toseq.stk > 2 report "XXX B"
    let second = top.stk
    let first = top.pop.stk,
    let val = if isempty.first ∧ e3 ∈ "/pre" then second else first + "/nsp" + second,
    next(haveatt, push(pop(stk, 2), val), acc, intag)
   else if e3 ∈ "/trim" then
    let t = "/sp /tag <br /tag > /nsp"
    let top = top.stk
    let val = if subseq(top, n.top - n.t + 1, n.top) = t then top >> n.t else top,
    let val2 = if subseq(val, 1, n.t) = t then val << n.t else val,
    next(haveatt, push(pop.stk, val2), acc, intag)
   else
    let result = dawsextensions:T(e3, stk),
    if not.isempty.result then next(haveatt, result, acc, intag)
    else
     let value = extractdef:T(defs, e3, content),
     next(haveatt, push(stk, value), acc, intag)
  else if intag then
   if isempty.haveatt then next([e3], stk, acc, intag)
   else
    let val = extractdef:T(defs, haveatt sub 1, content)
    assert haveatt ∈ ["rel", "class", "id", "alt"] report "val att:(haveatt)this" + e3 + acc >> (n.acc - 4),
    next([e3], stk, acc + attribute(val, haveatt sub 1), intag)
  else next(haveatt, stk, acc + extractdef:T(defs, e3, content), intag),
acc

function extractdef:T(defs:seq.word, name:word, content:seq.word) seq.word
if name ∈ "content" then content
else if name ∈ "colon" then ": "
else extractdef(defs, name) 