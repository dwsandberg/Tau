Module classinfo

precedence > for >1 >2

use UTF8

use bits

use seq.char

use seq.classinfo

use set.classinfo

use sort.classinfo

use seq.mark

use stack.mark

use standard

Export type:classinfo

Export type:tagorder

Export key(classinfo) word

Export baseon(classinfo) word

Export def(classinfo) seq.word

Export tag(classinfo) word

Export toseq(tagorder) seq.classinfo

type classinfo is key:word, baseon:word, def:seq.word, tag:word, flags:bits

type tagorder is toseq:seq.classinfo

The set.classinfo will be ordered by key. The taginfo will be ordered by tag. 

Function totagorder(a:seq.classinfo) tagorder tagorder.sort>3.a

Function lookuptag(lst:set.classinfo, tag:word) seq.classinfo
lookuptag(totagorder.toseq.lst, tag)

Function lookupkey(lst:set.classinfo, key:word) seq.classinfo
toseq.lookup(lst, classinfo(key, key, "", key, tobits.0))

Function lookuptag(s:tagorder, tag:word) seq.classinfo
let j = binarysearch>3(toseq.s, classinfo(tag, tag, "", tag, tobits.0)),
if j < 0 then empty:seq.classinfo
else
 for low = j, high = j, up = true, down = true
 while up ∨ down
 do
  let newdown = low > 1 ∧ tag = tag.(toseq.s) sub (low - 1)
  let newup = high < n.toseq.s ∧ tag = tag.(toseq.s) sub (high + 1)
  let newlow = if newdown then low - 1 else low,
  let newhigh = if newup then high + 1 else high,
  next(newlow, newhigh, newup, newdown),
 subseq(toseq.s, low, high)

Function %(a:classinfo) seq.word escapeFormat([key.a, baseon.a, tag.a] + def.a)

Function >1(a:classinfo, b:classinfo) ordering key.a >1 key.b

function >3(a:classinfo, b:classinfo) ordering tag.a >1 tag.b

function =(a:classinfo, b:classinfo) boolean key.a = key.b

Function tokey(w:word) word
let a = decodeword.w,
if a sub 2 = char1."/" then w else encodeword([char1."/"] + decodeword.w << 1)

Function classinfo2(
base:set.classinfo
, ele:word
, class:word
, more:seq.word
) seq.classinfo
let flagdefs = extractdef(more, "flags" sub 1)
for flags = tobits.0, w ∈ flagdefs
do
 let str = "mark noendtag define namedmark nocontent"
 let i = findindex(str, w),
 if i > n.str then flags else flags ∨ tobits.2 sup i,
if class ∈ "daws" then
 let key = merge("/" + ele)
 let tag = merge("<" + ele)
 let more1 =
  if subseq(more, 1, 2) = "flags: " then
   let i = min(findindex(more << 2, ":" sub 1), findindex(more << 2, ": " sub 1)),
   if i + 2 > n.more then "" else more << i
  else more,
 let a = classinfo(key, key, more1, tag, flags),
 if noendtag.a ∨ isdefine.a then [a]
 else
  let endtag = encodeword([char1."<", char1."/"] + decodeword.ele + char1.">")
  let namedtag = merge("//" + ele),
  if ismark.a then [a, classinfo(endtag, tag, "", endtag, flags ∨ tobits.1)]
  else if isnamedmark.a then
   [
    a
    , classinfo(endtag, tag, "", endtag, tobits.1)
    , classinfo(namedtag, key, "", namedtag, tobits.16)
   ]
  else [a, classinfo(endtag, tag, "", endtag, tobits.1)]
else
 let key = merge("/" + class)
 let basekey = merge("/" + ele)
 let info2 = lookupkey(base, basekey)
 assert not.isempty.info2 report escapeFormat("no base class key basekey:" + basekey + "key:" + key + "ele:" + ele)
 let baseclass = info2 sub 1
 for newdefs = "class", last = "?", e ∈ more
 do next(if e ∈ ": " then newdefs + last else newdefs, [e])
 {newdefs is a list of definitions included in the new class definition}
 for skip = false, basedefs = "", last1 = "", e ∈ def.baseclass + "dummy: "
 do
  if e ∉ ": " then next(skip, if skip then basedefs else basedefs + last1, [e])
  else if not.isempty.last1 ∧ last1 sub 1 ∈ newdefs then next(true, basedefs, "")
  else next(false, basedefs + last1, [e])
 {basedefs >> 1 is a list of definitions included in base but not in the new definition}
 let y =
  classinfo(
   key
   , basekey
   , "class: " + class + more + basedefs >> 1
   , tag.baseclass
   , if isempty.flagdefs then flags.baseclass else flags
  ),
 if isnamedmark.y then
  let namedtag = merge("//" + class),
  [y, classinfo(namedtag, basekey, "", namedtag, tobits.16)]
 else [y]

Function isendtag(a:classinfo) boolean (flags.a ∧ bits.1) = bits.1

Function ismark(a:classinfo) boolean (flags.a ∧ bits.2) = bits.2

Function noendtag(a:classinfo) boolean (flags.a ∧ bits.4) = bits.4

Function isdefine(a:classinfo) boolean (flags.a ∧ bits.8) = bits.8

Function isnamedmark(a:classinfo) boolean (flags.a ∧ bits.16) = bits.16

Function isnocontent(a:classinfo) boolean (flags.a ∧ bits.32) = bits.32

Function print(t:seq.classinfo) seq.word
for acc = "", e ∈ t
do
 if isendtag.e then acc
 else
  let flags =
   (if ismark.e then "mark" else "")
   + (if noendtag.e then "noendtag" else "")
   + (if isdefine.e then "define" else "")
   + (if isnamedmark.e then "namedmark" else "")
  let flags1 = if isempty.flags then "" else "flags: :(flags)",
  acc
  + [encodeword(decodeword.baseon.e << 1)]
  + ".daws{/* daws:(flags1):(def.e)*/}"
  + "/br",
acc

Function extractdef(defs:seq.word, name:word) seq.word
for notdone = true, found = false, acc = "", e ∈ defs + "dummy: "
while notdone
do
 if found then if e ∈ ": " then next(false, found, acc >> 1) else next(notdone, found, acc + e)
 else if e = name then next(notdone, found, [e])
 else if e ∈ ": " then
  if name ∈ subseq(acc, 1, 1) then {found}next(notdone, true, "")
  else next(notdone, found, ": ")
 else next(notdone, found, [e]),
if not.found then "" else acc

Function processCSS(z:seq.seq.word, dd:seq.classinfo) seq.classinfo
for acc = dd, p ∈ z
do
 for acc1 = acc, idx = findindex(p, "{" sub 1)
 while idx ≤ n.p
 do
  let new =
   if idx > n.p ∨ idx < 4 ∨ p sub (idx - 2) ∉ "." ∨ p sub (idx - 3) ∈ "}*/" then acc1
   else
    assert p sub (idx - 1) ∉ "daws" ∨ subseq(p, idx + 1, idx + 2) = "/* daws" report
     "In css file when defining how a new element:"
     + "(subseq(p, idx-3, idx), daws requires instructions in a comment of form: /* daws... */"
    let more =
     if subseq(p, idx + 1, idx + 2) = "/* daws" then subseq(p, idx + 3, idx + findindex(p << idx, "*/" sub 1) - 1)
     else "",
    acc1
    + classinfo2(asset.acc1, {ele}p sub (idx - 3), {class}p sub (idx - 1), more),
  next(new, idx + findindex(p << idx, "{" sub 1)),
 acc1,
acc

Function defaults seq.classinfo
let data =
 "q.daws{/* daws flags: mark output: <q class id > content </q> totxt: = content /mark = class */}/br
 b.daws{/* daws flags: mark output: <b class id > content </b> totxt: = content /mark = class */}/br
 i.daws{/* daws flags: mark output: <i class id > content </i> totxt: = content /mark = class */}/br
 em.daws{/* daws flags: mark output: <em class id > content </em> totxt: = content /mark = class */}/br
 strong.daws{/* daws flags: mark output: <strong class id > content </strong> totxt: = content /mark = t class */}/br
 span.daws{/* daws flags: mark output: <span class id > content </span> totxt: = content /mark = id class */}/br
 span.spc{/* daws output: <span class > /sp content /sp </span> */}/br
 caption.daws{/* daws flags: namedmark output: <caption class id > content </caption> totxt: content class */}/br
 a.daws{/* daws flags: mark output: <a class id href = href = > content </a> totxt: = content /mark = href class */}/br
 sub.daws{/* daws flags: mark output: <sub class id > content </sub> totxt: = content /mark = class */}/br
 sup.daws{/* daws flags: mark output: <sup class id > content </sup> totxt: = content /mark = class */}/br
 !doctype.daws{/* daws flags: noendtag */}/br
 meta.daws{/* daws flags: noendtag */}/br
 !.daws{/* daws flags: noendtag */}/br
 html.daws{/* daws */}/br
 body.daws{/* daws */}/br
 ?xml.daws{/* daws flags: noendtag */}/br
 head.daws{/* daws <body>: /tag <body> output: <head > content </head> <body> totxt: content */}/br
 link.daws{/* daws flags: noendtag rel: stylesheet output: <link rel href = content = /> totxt: = href = class /br
 */}/br
 base.daws{/* daws flags: noendtag output: <base rel href = content = /> totxt: = href = class */}/br
 title.daws{/* daws output: <title class > content </title> totxt: content class /br
 */}/br
 hr.daws{/* daws flags: noendtag output: content <hr class /> totxt: content class /p
 */}/br
 br.daws{/* daws flags: noendtag output: content <br class id /> totxt: content id class /br
 */}/br
 img.daws{/* daws flags: mark noendtag alt: a picture output: <img class id alt src = prefix content /pre postfix /post = /> totxt: = prefix src postfix /post /pre /mark = id class */}/br
 style.daws{/* daws */}/br
 p.daws{/* daws output: <p class id > content </p> totxt: content id class */}/br
 h1.daws{/* daws flags: namedmark output: <h1 class id > content </h1> totxt: content id class /p
 */}/br
 h2.daws{/* daws output: <h2 class id > content </h2> totxt: content id class /p
 */}/br
 h3.daws{/* daws output: <h3 class id > content </h3> totxt: content id class /p
 */}/br
 h4.daws{/* daws output: <h4 class id > content </h4> totxt: content id class /p
 */}/br
 h5.daws{/* daws output: <h5 class id > content </h5> totxt: content id class /p
 */}/br
 h6.daws{/* daws output: <h6 class id > content </h6> totxt: content id class /p
 */}/br
 table.daws{/* daws flags: namedmark output: <table class id > content </table> totxt: = content /mark = id class /br
 */}/br
 li.daws{/* daws output: <li class id > content </li> totxt: content id class /p
 */}/br
 ol.daws{/* daws flags: namedmark output: <ol class id start > content </ol> totxt: = content /mark = id class /p
 */}/br
 ul.daws{/* daws flags: namedmark output: <ul class id > content </ul> totxt: = content /mark = id class /p
 */}/br
 div.daws{/* daws flags: namedmark output: <div class id > content </div> totxt: = content /mark = id class /p
 */}/br
 tr.daws{/* daws output: <tr class id > content </tr> totxt: content id class /br
 */}/br
 td.daws{/* daws output: <td class id > content </td> totxt: content id class */}/br
 th.daws{/* daws output: <th class id > content </th> totxt: content id class */}/br
 href.daws{/* daws flags: define /href: href output: /href colon content */}/br
 id.daws{/* daws flags: define /id: id output: /id colon content */}/br
 rel.daws{/* daws flags: define /rel: rel output: /rel colon content */}/br
 ",
processCSS([data], empty:seq.classinfo)

Function attribute(val:seq.word, att:word) seq.word
if isempty.val then "" else "/sp:(att)/nsp =:(dq + "/nsp" + val + dq)"

Export type:mark

Export kind(mark) word

Export place(mark) int

Export mark(word, int) mark

type mark is kind:word, place:int

Function %(m:mark) seq.word ":(kind.m):(place.m)"

Function push(s:stack.mark, i:int) stack.mark push(s, mark("mark" sub 1, i))

Function extractdef(defs:seq.word, name:word, content:seq.word) seq.word
if name ∈ "content" then content
else if name ∈ "colon" then ": "
else extractdef(defs, name)

Function errorMarkup(
message:seq.word
, acc:seq.word
, marks:stack.mark
, z:seq.seq.word
) seq.word
let bb = "/tag <p>"
for txt = "", pcount = 1, wcount = 1, mrk0 = toseq.marks, e ∈ acc
do
 for mrk = mrk0, marktxt0 = ""
 while not.isempty.mrk ∧ wcount = place.mrk sub 1
 do next(mrk << 1, marktxt0 + escapeFormat.[kind.mrk sub 1])
 let marktxt1 = if isempty.marktxt0 then marktxt0 else "/tag <p> <<" + marktxt0 + ">>",
 if e = encodeword.[char.10] then next(txt + bb + toword.pcount + marktxt1, pcount + 1, wcount + 1, mrk)
 else
  next(
   if e ∈ "/sp /nsp /tag" then txt + marktxt1 else txt + escapeFormat.[e] + marktxt1
   , pcount
   , wcount + 1
   , mrk
  )
for txt2 = "", e ∈ z sub pcount do txt2 + escapeFormat.[e],
red.message + "/p:(txt)/p PROCESSING PARAGRAPH:(txt2)/p:(red.message)"

Function escapeFormat(b:seq.word) seq.word
[escapeformat, encodeword.[char.32]] + b + [encodeword.[char.32], escapeformat] 