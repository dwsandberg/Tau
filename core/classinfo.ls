Module classinfo

precedence > for >1 >2

use bits

use seq.char

use seq.classinfo

use set.classinfo

use sort.classinfo

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

Function %(a:classinfo) seq.word esc.[key.a, baseon.a, tag.a] + def.a

Function >1(a:classinfo, b:classinfo) ordering key.a >1 key.b

function >3(a:classinfo, b:classinfo) ordering tag.a >1 tag.b

function =(a:classinfo, b:classinfo) boolean key.a = key.b

Function tokey(w:word) word
let a = decodeword.w,
if a sub 2 = char1."/" then w else encodeword([char1."/"] + decodeword.w << 1)

Function esc(z:seq.word) seq.word
for dd = "", e ∈ z
do
 if e
 ∈ "/p /br
 /sp /tag /keyword <* *>" then dd + "/sp /tag:(e)/sp"
 else dd + e,
dd

Function removeesc(z:seq.word) seq.word
for dd = "", e ∈ z
do
 if e
 ∈ "/p /br
 /sp /tag"
 ∧ subseq(dd, n.dd - 1, n.dd) = "/sp /tag" then dd >> 2 + e
 else dd + e,
dd

Function classinfo2(
base:set.classinfo
, ele:word
, class:word
, more:seq.word
) seq.classinfo
if class ∈ "daws" then
 let key = merge("/" + ele)
 let flags = extractdef(more, "flags" sub 1)
 for acc = 0, w ∈ flags
 do
  let str = "mark noendtag define namedmark"
  let i = findindex(str, w),
  if i > n.str then acc else acc + 2 sup i
 let tag = merge("<" + ele)
 let more1 =
  if subseq(more, 1, 2) = "flags: " then
   let i = min(findindex(more << 2, ":" sub 1), findindex(more << 2, ": " sub 1)),
   if i + 2 > n.more then "" else more << i
  else more,
 let a = classinfo(key, key, more1, tag, bits.acc),
 if noendtag.a ∨ isdefine.a then [a]
 else
  let endtag = encodeword([char1."<", char1."/"] + decodeword.ele + char1.">")
  let namedtag = merge("//" + ele),
  if ismark.a then [a, classinfo(endtag, tag, "", endtag, tobits(acc + 1))]
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
 assert not.isempty.info2 report esc."no base class key basekey:" + basekey + "key:" + key + "ele:" + ele
 let baseclass = info2 sub 1
 for newdefs = "class", last = "?", e ∈ more
 do next(if e ∈ ": " then newdefs + last else newdefs, [e])
 for skip = false, basedefs = "", last1 = "", e ∈ def.baseclass
 do
  if e ∉ ": " then next(skip, if skip then basedefs else basedefs + last1, [e])
  else if not.isempty.last1 ∧ last1 sub 1 ∈ newdefs then next(true, basedefs, "")
  else next(false, basedefs + last1, [e])
 {assert class ∈"pic xx picC slide name"∨ basedefs+last1 = def.baseclass report":(class)more"+more+"/p
 "+"base"+def.baseclass+"/p
 "+"newbase"+basedefs+last1}
 let y =
  classinfo(
   key
   , basekey
   , "class: " + class + more + basedefs + last1
   , tag.baseclass
   , flags.baseclass
  ),
 if isnamedmark.info2 sub 1 then
  let namedtag = merge("//" + class),
  [y, classinfo(namedtag, basekey, "", namedtag, tobits.16)]
 else [y]

Function isendtag(a:classinfo) boolean (flags.a ∧ bits.1) = bits.1

Function ismark(a:classinfo) boolean (flags.a ∧ bits.2) = bits.2

Function noendtag(a:classinfo) boolean (flags.a ∧ bits.4) = bits.4

Function isdefine(a:classinfo) boolean (flags.a ∧ bits.8) = bits.8

Function isnamedmark(a:classinfo) boolean (flags.a ∧ bits.16) = bits.16

function print(t:seq.classinfo) seq.word
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
for notdone = true, found = false, acc = "", e ∈ defs + "dummy:"
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
 caption.daws{/* daws flags: mark output: <caption class id > content </caption> totxt: = content /mark = class */}/br
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
 link.daws{/* daws flags: mark noendtag rel: stylesheet output: <link rel href = content = /> totxt: = href /mark = class */}/br
 base.daws{/* daws flags: mark noendtag output: <base rel href = content = /> totxt: = href /mark = class */}/br
 title.daws{/* daws output: <title class > content </title> totxt: content class /br
 */}/br
 hr.daws{/* daws flags: noendtag output: <hr class /> totxt: /p
 content class */}/br
 br.daws{/* daws flags: noendtag output: content <br class id /> totxt: content id class /br
 */}/br
 img.daws{/* daws flags: mark noendtag alt: a picture output: <img class id alt src = prefix content /pre postfix /post = /> totxt: = prefix src postfix /post /pre /mark = id class */}/br
 style.daws{/* daws */}/br
 p.daws{/* daws output: <p class id > content </p> totxt: /p
 content id class /p
 */}/br
 h1.daws{/* daws output: <h1 class id > content </h1> totxt: /p
 content id class */}/br
 h2.daws{/* daws output: <h2 class id > content </h2> totxt: /p
 content id class */}/br
 h3.daws{/* daws output: <h3 class id > content </h3> totxt: /p
 content id class */}/br
 h4.daws{/* daws output: <h4 class id > content </h4> totxt: /p
 content id class */}/br
 h5.daws{/* daws output: <h5 class id > content </h5> totxt: /p
 content id class */}/br
 h6.daws{/* daws output: <h6 class id > content </h6> totxt: /p
 content id class */}/br
 table.daws{/* daws output: <table class id > content </table> totxt: /p
 content id class */}/br
 li.daws{/* daws output: <li class id > content </li> totxt: /p
 content id class /p
 */}/br
 ol.daws{/* daws flags: namedmark output: <ol class id > content </ol> totxt: /p
 content id class /p
 */}/br
 ul.daws{/* daws flags: namedmark output: <ul class id > content </ul> totxt: /p
 content id class */}/br
 div.daws{/* daws flags: namedmark output: <div class id > content </div> totxt: /p
 = content /mark = id class */}/br
 tr.daws{/* daws output: <tr class id > content </tr> totxt: content id class /br
 */}/br
 td.daws{/* daws output: <td class id > content </td> totxt: content id class */}/br
 th.daws{/* daws output: <th class id > content </th> totxt: content id class */}/br
 href.daws{/* daws flags: define /href: href output: /href colon content */}/br
 id.daws{/* daws flags: define /id: id output: /id colon content */}/br
 rel.daws{/* daws flags: define /rel: rel output: /rel colon content */}/br
 ",
processCSS([data], empty:seq.classinfo) 