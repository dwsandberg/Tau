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
do next(if w ∈ "/base /link /title /meta" then idx else header, idx + 1)
let newz = [subseq(p1, 1, header) + "/head", p1 << header] + z << 1
let final = textFormat1a(if xhtml then "/tag </body></html>" else ""),
textFormat1a(
 if xhtml then "<?xml version =:(dq."1.0")encoding =:(dq."utf-8")?> <html xmlns =:(dq."http://www.w3.org/1999/xhtml")xmlns:epub =:(dq."http://www.idpf.org/2007/ops")>"
 else "<!doctype html> <html lang /nsp =:(dq.":(lang)")> <meta charset /nsp =:(dq."utf-8")>"
)
 + HTMLformat1a.txt2html:T(newz, asset.replacements, xhtml)
 + final

function showZ:T(out:seq.word) seq.word
for acc = "", w ∈ out do acc + encodeword(decodeword.w + char1."Z"),
acc

Function txt2html:T(z:seq.seq.word, replacements:set.classinfo, xhtml:boolean) seq.word
{covert paragraph to html}
let gdefatt = lookupkey(replacements, "/global$defs" sub 1)
let globaldefs = if isempty.gdefatt then "" else def.gdefatt sub 1
let pdef = def.lookupkey(replacements, "/p" sub 1) sub 1
for acc0 = "", mark0 = push(empty:stack.mark, mark("block" sub 1, 0)), pno = 1, p ∈ z
do
 for
  last = "?" sub 1
  , skip = false
  , defines = ""
  , marks = mark0
  , acc = acc0
  , e ∈ p + "/p"
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
     evaldef:T(
      subseq(acc, 1, place)
      , defines + pdef
      , content
      , replacements
      , xhtml
      , subseq(z, 1, pno)
     )
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
      evaldef:T(
       if isdefine.att then "" else smallacc
       , combinedDef
       , content
       , replacements
       , xhtml
       , subseq(z, 1, pno)
      ),
     let stk2 = if nomark then marks else pop.marks,
     if isdefine.att then next(e, skip, defines + new, stk2, smallacc)
     else next(e, skip, "", stk2, new)
    else
     for acc1 = acc, ee ∈ [1]
     while basedon ∈ "/div" ∧ kind.top.marks ∈ "block" ∧ place.top.marks < n.acc1
     do
      let content = subseq(acc1, place.top.marks + 1, n.acc1),
      acc1 >> n.content + "/tag <p>" + content
     let marks1 =
      if basedon ∈ "/caption" ∧ kind.top.marks ∈ "mark" then pop.marks
      else if basedon ∈ "/div /li" ∧ kind.top.marks ∈ "block" then pop.marks
      else if basedon ∈ "/ol /ul" then
       for marks1 = marks
       while kind.top.marks1 ∈ "block /li" ∧ place.top.marks1 = n.acc1
       do pop.marks1,
       marks1
      else if basedon ∈ "/li" ∧ kind.top.marks ∈ "block" then pop.marks
      else if basedon ∈ "/td" ∧ kind.top.marks ∈ "/th" then push(pop.marks, mark(basedon, place.top.marks))
      else if basedon ∈ "/td" ∧ kind.top.marks ∈ "block" then pop.marks
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
      evaldef:T(
       if isdefine.att then "" else smallacc
       , combinedDef
       , content
       , replacements
       , xhtml
       , subseq(z, 1, pno)
      )
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
smallacc:seq.word
, defs:seq.word
, content:seq.word
, replacements:set.classinfo
, xhtml:boolean
, raw:seq.seq.word
) seq.word
let evalstr = extractdef(defs, "output" sub 1)
for
 haveatt = ""
 , stk = empty:stack.seq.word
 , acc = smallacc
 , intag = false
 , litval = ""
 , e3 ∈ evalstr + "?"
do
 if e3 ∈ "=" then
  if isempty.stk then next(haveatt, push(stk, "bottom"), acc, intag, litval)
  else if intag ∧ not.isempty.haveatt then next("", empty:stack.seq.word, acc + attribute(top.stk, haveatt sub 1), intag, litval)
  else next(haveatt, empty:stack.seq.word, acc + top.stk, intag, litval)
 else
  let info = lookuptag(replacements, e3),
  if not.isempty.info then
   if isendtag.info sub 1 then
    let new = if xhtml ∨ e3 ∉ "</p> </li>" then acc + "/tag" + e3 else acc,
    next(haveatt, stk, new, intag, litval)
   else
    {assert e3 ∈"<titlex"report"here gg JKL:(e3):(intag, litval)"+acc+"/p"+evalstr}
    let acc1 =
     if e3 ∈ "<sub <sup" then if last.acc ∈ "/tag" then acc + e3 else acc + "/tag" + e3
     else acc + "/tag" + e3,
    next("", stk, acc1, true, litval)
  else if e3 ∈ "> />" then
   let end = if xhtml ∧ e3 ∈ "/>" then "/tag />" else "/tag >"
   let lastatt =
    if not.isempty.haveatt ∧ intag then acc + attribute(extractdef(defs, haveatt sub 1, content), haveatt sub 1)
    else acc,
   next("", stk, lastatt + end, false, litval)
  else if not.isempty.stk then
   if e3 ∈ "'" then
    if isempty.litval then next(haveatt, stk, acc, intag, "'")
    else next(haveatt, push(stk, litval << 1), acc, intag, "")
   else if not.isempty.litval then next(haveatt, stk, acc, intag, litval + e3)
   else if e3 ∈ "/post /pre" then
    {designed to add directory and extension to file names}
    assert n.toseq.stk > 2 report "XXX B"
    let second = top.stk
    let first = top.pop.stk,
    let val =
     if e3 ∈ "pre" then
      if isempty.second ∨ first << (n.first - n.second) = second ∨ second sub 1 ∈ first then first
      else first + second
     else if isempty.first then second
     else first + "/nsp" + second,
    next(haveatt, push(pop(stk, 2), val), acc, intag, litval)
   else if e3 ∈ "/trim" then
    let t = "/sp /tag <br /tag >"
    let top = top.stk
    let val = if subseq(top, n.top - n.t + 1, n.top) = t then top >> n.t else top,
    let val2 = if subseq(val, 1, n.t) = t then val << n.t else val,
    next(haveatt, push(pop.stk, val2), acc, intag, litval)
   else if e3 ∈ "/raw" then
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
     next(
      p1
      + "/br /br
      "
      + txt
      , end
     ),
    next(haveatt, push(stk, txt >> 2), acc, intag, litval)
   else if e3 ∈ "/css" then
    for p = "", save = "", state = 0, w ∈ top.stk
    do
     if w ∈ "/*" then next(p + w, save, 3)
     else if w ∈ "*/" ∧ state = 3 then next(p + w, save, 0)
     else if w ∈ ": " ∧ state ∈ [0, 3] then next(p + w, save, state + 1)
     else if w ∈ ":" ∧ state = 0 then next(p + w, save, 1)
     else if w ∈ ";}" ∧ state = 1 ∨ w ∈ ": */" ∧ state = 4 then
      let save1 = if w ∈ ": " then save >> 1 else save
      let tmp =
       "/tag <span:(attribute("attval", "class" sub 1))/tag >:(escapeFormat.save1)/tag </span>",
      let newstate =
       if w ∈ ";}" ∧ state = 1 then 0 else if w ∈ "*/" ∧ state = 4 then 0 else state,
      next(p + tmp + save << n.save1 + w, "", newstate)
     else if state ∈ [1, 4] then next(p, save + w, state)
     else next(p + w, save, state),
    next(haveatt, push(pop.stk, p + save), acc, intag, litval)
   else
    let result = dawsextensions:T(e3, stk),
    if not.isempty.result then next(haveatt, result, acc, intag, litval)
    else
     let value = extractdef(defs, e3, content),
     next(haveatt, push(stk, value), acc, intag, litval)
  else if intag then
   if isempty.haveatt then next([e3], stk, acc, intag, litval)
   else
    let val = extractdef(defs, haveatt sub 1, content)
    {assert haveatt ∈["rel","class","id","alt"]report"val att:(haveatt)this"+e3+acc >>(n.acc-4),}
    next([e3], stk, acc + attribute(val, haveatt sub 1), intag, litval)
  else next(haveatt, stk, acc + extractdef(defs, e3, content), intag, litval),
acc 