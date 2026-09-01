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

use seq1.pair

use standard

use seq.word

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
if class ∈ "daws" ∨ class = ele then
 let key = merge("/" + ele)
 let tag = merge("<" + ele)
 let more1 =
  if subseq(more, 1, 2) = "flags: " then
   let i = min(findindex(more << 2, ":" sub 1), findindex(more << 2, ": " sub 1)),
   if i + 2 > n.more then "" else more << i
  else more,
 let a = classinfo(key, key, more1, tag, flags),
 if isdefine.a then [classinfo(key, key, more1, key, flags)]
 else if noendtag.a then [a]
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
   , {basekey}baseon.baseclass
   , "class: " + class + more + basedefs >> 1
   , tag.baseclass
   , if isempty.flagdefs then flags.baseclass else flags
  ),
 if isnamedmark.y then
  let namedtag = merge("//" + class),
  [y, classinfo(namedtag, {basekey}baseon.baseclass, "", namedtag, tobits.16)]
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
   + (if isnocontent.e then "nocontent" else "")
  let flags1 = if isempty.flags then "" else "flags: :(flags)",
  let class = extractdef(def.e, "class" sub 1),
  acc
  + ":(encodeword(decodeword.baseon.e << 1)).:(if isempty.class then "daws" else class){/* daws:(flags1):(escapeFormat.def.e)*/}"
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
  let more =
   if subseq(p, idx + 1, idx + 2) = "/* daws" then subseq(p, idx + 3, idx + findindex(p << idx, "*/" sub 1) - 1)
   else ""
  let new =
   if (idx = 2 ∨ p sub (idx - 2) ∈ "}/br") ∧ not.isempty.more then classinfo2(asset.acc1, {ele}p sub (idx - 1), {class}p sub (idx - 1), more) + acc1
   else if idx > n.p ∨ idx < 4 ∨ p sub (idx - 2) ∉ "." ∨ p sub (idx - 3) ∈ "}*/" then acc1
   else
    assert p sub (idx - 1) ∉ "daws" ∨ subseq(p, idx + 1, idx + 2) = "/* daws" report
     "In css file when defining how a new element:"
     + "(subseq(p, idx-3, idx), daws requires instructions in a comment of form: /* daws... */",
    classinfo2(asset.acc1, {ele}p sub (idx - 3), {class}p sub (idx - 1), more) + acc1,
  next(new, idx + findindex(p << idx, "{" sub 1)),
 acc1,
acc

Function defaults seq.classinfo
let data =
 "q{/* daws flags: mark tohtml: < q class id > content </ q > totxt: content /mark id /id class */}:($$)
 b{/* daws flags: mark tohtml: < b class id > content </ b > totxt: content /mark id /id class */}:($$)
 i{/* daws flags: mark tohtml: < i class id > content </ i > totxt: content /mark id /id class */}:($$)
 em{/* daws flags: mark tohtml: < em class id > content </ em > totxt: content /mark id /id class */}:($$)
 strong{/* daws flags: mark tohtml: < strong class id > content </ strong > totxt: content /mark id /id class */}:($$)
 span{/* daws flags: mark tohtml: < span class id > content </ span > totxt: content /mark id /id class */}:($$)
 span.spc{/* daws flags: mark tohtml: /sp < span class id > content </ span > /sp */}:($$)
 caption{/* daws flags: namedmark tohtml: < caption class id > content </ caption > totxt: content class */}:($$)
 a{/* daws flags: mark tohtml: < a class id href > content </ a > totxt: content /mark href /href class */}:($$)
 sub{/* daws flags: mark tohtml: /nsp < sub class id > content </ sub > totxt: content /mark id /id class */}:($$)
 sup{/* daws flags: mark tohtml: /nsp < sup class id > content </ sup > totxt: content /mark id /id class */}:($$)
 !doctype{/* daws flags: noendtag */}:($$)
 meta{/* daws flags: noendtag */}:($$)
 !{/* daws flags: noendtag */}:($$)
 html{/* daws tohtml: content </ html > */}:($$)
 body{/* daws flags: */}:($$)
 ?xml{/* daws flags: noendtag */}:($$)
 head{/* daws tohtml: < head > content </ head > < body > totxt: content /p */}:($$)
 link{/* daws flags: noendtag rel: stylesheet tohtml: < link rel href:content /> totxt: href /mark class /br */}:($$)
 base{/* daws flags: noendtag tohtml: < base rel href:content /> totxt: href /mark class */}:($$)
 title{/* daws tohtml: < title class > content </ title > totxt: content class /br */}:($$)
 hr{/* daws flags: noendtag tohtml: content < hr class /> totxt: content class /p */}:($$)
 br{/* daws flags: noendtag tohtml: content < br class id /> totxt: content id /id class /br */}:($$)
 br.eol{/* daws totxt: content /eol /br */}:($$)
 img{/* daws flags: mark noendtag alt: a picture tohtml: < img class id alt src:prefix content /pre postfix /post /> totxt: prefix src postfix /post /pre /mark id /id class */}:($$)
 style{/* daws */}:($$)
 p{/* daws tohtml: < p class id > content </ p > totxt: content id /id class /p */}:($$)
 h1{/* daws flags: namedmark tohtml: < h1 class id > content </ h1 > totxt: content id /id class /p */}:($$)
 h2{/* daws tohtml: < h2 class id > content </ h2 > totxt: content id /id class /p */}:($$)
 h3{/* daws tohtml: < h3 class id > content </ h3 > totxt: content id /id class /p */}:($$)
 h4{/* daws tohtml: < h4 class id > content </ h4 > totxt: content id /id class /p */}:($$)
 h5{/* daws tohtml: < h5 class id > content </ h5 > totxt: content id /id class /p */}:($$)
 h6{/* daws tohtml: < h6 class id > content </ h6 > totxt: content id /id class /p */}:($$)
 table{/* daws flags: namedmark tohtml: < table class id > content </ table > totxt: content /mark id /id class /br */}:($$)
 li{/* daws tohtml: < li class id > content </ li > totxt: content id /id class /p */}:($$)
 ol{/* daws flags: namedmark tohtml: < ol class id start > content </ ol > totxt: content /mark id /id class /p */}:($$)
 ul{/* daws flags: namedmark tohtml: < ul class id > content </ ul > totxt: content /mark id /id class /p */}:($$)
 div{/* daws flags: namedmark tohtml: < div class id > content </ div > totxt: content /mark id /id class /p */}:($$)
 div.noformat{/* daws tohtml: < div class id > /raw /escape/ </ div > totxt: content /escape/ /mark id /id class */ display:inline;}:($$)
 tr{/* daws tohtml: < tr class id > content </ tr > totxt: content id /id class /br */}:($$)
 td{/* daws tohtml: < td class id > content </ td > totxt: content id /id class */}:($$)
 th{/* daws tohtml: < th class id > content </ th > totxt: content id /id class */}:($$)
 href{/* daws flags: define tohtml: ' href colon content */}:($$)
 id{/* daws flags: define tohtml: ' id colon content */}:($$)
 rel{/* daws flags: define tohtml: ' rel colon content */}:($$)
 meta.charset{/* daws tohtml: < meta charset:content; > */}:($$)
 input{/* daws flags: noendtag type: hidden tohtml: content < input type /> totxt: content type /type class */}",
processCSS([data], empty:seq.classinfo)

Function attribute(val:seq.word, att:seq.word) seq.word
if isempty.val then "" else "/sp:(att)/nsp =:(dq + "/nsp" + val + dq)"

Export type:mark

Export kind(mark) word

Export place(mark) int

Export mark(kind:word, place:int) mark

type mark is kind:word, place:int

Function %(m:mark) seq.word ":(kind.m):(place.m)"

Function push(s:stack.mark, i:int) stack.mark push(s, mark("mark" sub 1, i))

type pair is name:seq.word, value:seq.word

Export type:pair

Function %(a:pair) seq.word "@:(name.a)::(value.a);"

Function =(a:pair, b:pair) boolean name.a = name.b

Export pair(name:seq.word, value:seq.word) pair

Export name(pair) seq.word

Export value(pair) seq.word

Function getDefines(a:seq.word) seq.pair
for acc = empty:seq.pair, name = "", nextName = "", val = "", e ∈ a + "dummy: "
do
 if e ∈ ": " then next(if not.isempty.name then acc + pair(name, val) else acc, nextName, "", "")
 else if e ∈ ".-" then next(acc, name, nextName + e, val)
 else if isempty.nextName ∨ last.nextName ∉ ".-" then next(acc, name, [e], val + nextName)
 else next(acc, name, nextName + e, val),
acc

Function extractdef(a:seq.pair, name:seq.word) seq.word
let j = lookup(a, pair(name, "")),
if isempty.j then "" else value.j sub 1

Function getToHTMLexpression(alldefs:seq.pair) seq.pair
let a = extractdef(alldefs, "tohtml")
let r = parse(a, empty:seq.pair)
assert status.r ∈ "Match" report "BB parse error:(a)",
result.r

Export type:stkinfo

Export info(stkinfo) classinfo

Export place(stkinfo) int

Export tagcontent(stkinfo) seq.word

Export stkinfo(classinfo, seq.word, int) stkinfo

type stkinfo is info:classinfo, tagcontent:seq.word, place:int

Function getAtt(txt:seq.word) seq.pair
let inname = 0
let invalue = 1
let indq = 2
for
 acc = empty:seq.pair
 , name = ""
 , state = inname
 , val = ""
 , e ∈ subseq(txt, 2, n.txt - 1)
do
 if state = inname then
  if e ∈ "=" then next(acc, name, invalue, val)
  else next(acc, name + e, state, val)
 else if e ∈ dq then
  if state = invalue then next(acc, name, indq, val)
  else next(acc + pair(name, val), "", inname, "")
 else next(acc, name, state, val + e),
acc

Function rmprefix(prefix0:seq.word, A:seq.word) seq.word
if isempty.prefix0 then A
else
 let prefix = if last.prefix0 ∈ "/nsp" then prefix0 >> 1 else prefix0,
 if n.A < n.prefix then A
 else
  for B = A, prefix1 = prefix
  while not.isempty.prefix1 ∧ prefix1 sub 1 = B sub 1
  do next(B << 1, prefix1 << 1),
  if isempty.prefix1 ∨ isempty.B then B
  else
   let m1 = decodeword.prefix1 sub 1
   let m2 = decodeword.B sub 1,
   if subseq(m2, 1, n.m1) = m1 then [encodeword(m2 << n.m1)] + B << 1 else B

Function rmpostfix(t:seq.word, postfix:seq.word) seq.word
if n.t < n.postfix then t
else
 for A = t, postfix1 = postfix
 while not.isempty.postfix1 ∧ last.postfix1 = last.A
 do next(A >> 1, postfix >> 1),
 A

function endMark word encodeword.[char.254]

function toAttribute(a:seq.pair, b:seq.word) seq.pair [pair("", b)]

function e?(a:seq.pair) seq.pair
if isempty.a then a
else if isempty.value.last.a ∧ isempty.name.last.a then a >> 1
else if isempty.value.first.a ∧ isempty.name.first.a then a >> 1
else a

function endtag(a:seq.word) seq.word
"/!<:(if a = "p" then escapeFormat."/p" + "/!>" else [merge."/:(a)"] + "/!>")"

function +(acc:seq.pair, s:seq.word) seq.pair
if isempty.acc then [pair("", s)]
else
 assert not(isempty.value.last.acc ∧ isempty.name.last.acc) report "JJK:",
 if not.isempty.acc ∧ isempty.name.last.acc then acc >> 1 + pair("", value.last.acc + s)
 else acc + pair("", s)

function tag(acc:seq.pair, name:seq.pair, a:seq.pair, end:seq.word) seq.pair
assert not.isempty.acc report "here"
let combine = name.last.acc = "no eval" ∨ isempty.value.last.acc ∧ isempty.name.last.acc
let acc1 = if combine then acc >> 1 else acc
let more = if combine then value.last.acc else "",
if isempty.a then acc1 + pair("no eval", more + endtag.value.first.name)
else acc1 + pair("no eval", more + "/!<" + value.first.name) + a + pair("no eval", end)

function first(a:seq.pair) pair a sub 1

function genPEG(seqElementType:word, attributeType:seq.pair) seq.boolean
{wordmap: "$"sub 1}
[
 "* S < any C1 >" = tag($.0, $.1, $.2, "/!>")
 , "/ < any C1 />" = tag($.0, $.1, $.2, "/ /!>")
 , "/ </ any >" = tag($.0, $.1, empty:seq.pair, "/!>")
 , "/ ! < ! </ any" = e?.$.0 + value.first.$.1
 , "* C1 N2:V;" = e?.$.0 + pair(value.first.$.1, value.first.$.2)
 , "/ N2:V" = e?.$.0 + pair(value.first.$.1, value.first.$.2)
 , "/ N2" = e?.$.0 + pair(value.first.$.1, value.first.$.1)
 , "N2 N1 N1'" = [pair("", value.first.$.1 + value.first.$.2)]
 , "* N1'-any" = [pair("", value.first.$.0 + "-" + value.first.$.1)]
 , "N1 ! > ! /> any" = $.1
 , "* V !; ! > ! /> any" = /All
]

<<<< Below is auto generated code >>>>

/eol
Non-terminals:C1 N1 N1' N2 S V /eol
Terminals://noformat-/>:; < </ > any /noformat /eol
//noformat * S ← < any C1 > / < any C1 /> / </ any > / ! < ! </ any /noformat /eol
* C1 ← N2:V; / N2:V / N2 /eol
N2 ← N1 N1' /eol
* N1' ←-any /eol
//noformat N1 ← ! > ! /> any /noformat /eol
//noformat * V ← !; ! > ! /> any /noformat /eol

function action(partno:int, R:seq.seq.pair) seq.pair
if partno = 2 then tag(R sub (n.R - 2), R sub (n.R - 1), R sub n.R, "/!>")
else if partno = 3 then tag(R sub (n.R - 2), R sub (n.R - 1), R sub n.R, "/ /!>")
else if partno = 4 then tag(R sub (n.R - 1), R sub n.R, empty:seq.pair, "/!>")
else if partno = 5 then e?.R sub (n.R - 1) + value.first.R sub n.R
else if partno = 6 then e?.R sub (n.R - 2) + pair(value.first.R sub (n.R - 1), value.first.R sub n.R)
else if partno = 7 then e?.R sub (n.R - 2) + pair(value.first.R sub (n.R - 1), value.first.R sub n.R)
else if partno = 8 then e?.R sub (n.R - 1) + pair(value.first.R sub n.R, value.first.R sub n.R)
else if partno = 9 then [pair("", value.first.R sub (n.R - 1) + value.first.R sub n.R)]
else if partno = 10 then [pair("", value.first.R sub (n.R - 1) + "-" + value.first.R sub n.R)]
else if partno = 11 then R sub n.R
else R sub 1

function mytable seq.tableEntry
[
 {1}tableEntry(NT.T'.2, "?" sub 1, Match, Failure, "")
 , {2}tableEntry(T', "<" sub 1, MatchAny.3, T.10, "")
 , {3}tableEntry(MatchAny, "?" sub 1, NT.4, T'.6, "")
 , {4}tableEntry(NT.16, "C1" sub 1, T'.5, S'.T.10, "")
 , {5}tableEntry(T', ">" sub 1, Reduce*(2, T'.2), T.9, "")
 , {6}tableEntry(T', "<" sub 1, MatchAny.7, T.10, "")
 , {7}tableEntry(MatchAny, "?" sub 1, NT.8, T.10, "")
 , {8}tableEntry(NT.16, "C1" sub 1, T.9, T.10, "")
 , {9}tableEntry(T, "/>" sub 1, Reduce*(3, T'.2), T.10, "")
 , {10}tableEntry(T, "</" sub 1, MatchAny.11, !T.13, "")
 , {11}tableEntry(MatchAny, "?" sub 1, T.12, !T.13, "")
 , {12}tableEntry(T, ">" sub 1, Reduce*(4, T'.2), !T.13, "")
 , {13}tableEntry(!T, "<" sub 1, Success*, !T.14, "")
 , {14}tableEntry(!T, "</" sub 1, Success*, MatchAny.15, "")
 , {15}tableEntry(MatchAny, "?" sub 1, Reduce*(5, T'.2), Success*, "")
 , {16}tableEntry(NT.24, "N2" sub 1, T'.17, Success*, "")
 , {17}tableEntry(T', ":" sub 1, NT.18, T.21, "")
 , {18}tableEntry(NT.!T.31, "V" sub 1, T.19, S'.NT.23, "")
 , {19}tableEntry(T, ";" sub 1, Reduce*(6, NT.16), NT.20, "")
 , {20}tableEntry(NT.24, "N2" sub 1, T.21, Success*, "")
 , {21}tableEntry(T, ":" sub 1, NT.22, NT.23, "")
 , {22}tableEntry(NT.!T.31, "V" sub 1, Reduce*(7, NT.16), NT.23, "")
 , {23}tableEntry(NT.24, "N2" sub 1, Reduce*(8, NT.16), Success*, "")
 , {24}tableEntry(NT.!T.28, "N1" sub 1, NT.25, Fail, "")
 , {25}tableEntry(NT.T.26, "N1'" sub 1, Reduce.9, Fail, "")
 , {26}tableEntry(T, "-" sub 1, MatchAny.27, Success*, "")
 , {27}tableEntry(MatchAny, "?" sub 1, Reduce*(10, T.26), Success*, "")
 , {28}tableEntry(!T, ">" sub 1, Fail, !T.29, "")
 , {29}tableEntry(!T, "/>" sub 1, Fail, MatchAny.30, "")
 , {30}tableEntry(MatchAny, "?" sub 1, Reduce.11, Fail, "")
 , {31}tableEntry(!T, ";" sub 1, All, !T.32, "")
 , {32}tableEntry(!T, ">" sub 1, All, !T.33, "")
 , {33}tableEntry(!T, "/>" sub 1, All, MatchAny.34, "")
 , {34}tableEntry(MatchAny, "?" sub 1, Discard*.!T.31, All, "")
]

function =(seq.word, seq.pair) boolean true

function $(int) seq.pair empty:seq.seq.pair sub 1

use standard

use seq.tableEntry

use seq1.frame

use stack.frame

use seq1.seq.pair

use PEGrules

function place(r:resultType) int i.top.stk.r

type frame is
Sstate:state
, Fstate:state
, i:int
, result:seq.seq.pair
, faili:int
, failresult:seq.seq.pair

type resultType is stk:stack.frame

Function status(a:resultType) word
if Sstate.top.stk.a ≠ Match then 'Failed
else if place.a = {length of input}faili.top.stk.a then 'Match
else 'MatchPrefix

Function result(a:resultType) seq.pair last.result.top.stk.a

function parse(myinput0:seq.word, initAttr:seq.pair) resultType
let myinput = packed(myinput0 + endMark)
let packedTable = packed.mytable
for
 stk = empty:stack.frame
 , state = startstate
 , i = 1
 , inputi = myinput sub 1
 , result = [initAttr]
 , faili = 1
 , failresult = [initAttr]
while toint.state > toint.Match
do
 let actionState = action.state,
 if actionState = Fail then
  {goto Fstate.top.stk, i = faili.top, pop.stk, discard result}
  let top = top.stk,
  if toint.action.Fstate.top ≥ toint.S' then
   let newi = i.top,
   next(
    pop.stk
    , nextState.Fstate.top
    , newi
    , idxNB(myinput, newi)
    , result.top
    , faili.top
    , failresult.top
   )
  else
   next(
    pop.stk
    , Fstate.top
    , faili.top
    , idxNB(myinput, faili.top)
    , failresult.top
    , faili.top
    , failresult.top
   )
 else if actionState = Success* then
  {goto Sstate.top.stk, pop.stk, keep result}
  let top = top.stk,
  next(pop.stk, Sstate.top, i, inputi, result.top + result, faili.top, failresult.top)
 else if actionState = Discard* then
  let top = top.stk,
  next(stk, nextState.state, i, inputi, result.top, i, result.top)
 else if actionState = All then
  let top = top.stk
  let att = [toAttribute(result sub n.result, subseq(myinput, i.top, i - 1))],
  next(pop.stk, Sstate.top, i, inputi, result.top + att, faili.top, failresult.top)
 else if actionState = Lambda then
  let att = [action(reduceNo.state, result)],
  next(stk, nextState2.state, i, inputi, result + att, faili, failresult)
 else if actionState = Reduce then
  let top = top.stk
  let att = [action(reduceNo.state, result)],
  next(pop.stk, Sstate.top, i, inputi, result.top + att, faili.top, failresult.top)
 else if actionState = Reduce* then
  let att = [action(reduceNo.state, result)]
  let top = top.stk,
  next(stk, nextState.state, i, inputi, att, i, att)
 else if actionState = !Reduce then
  let top = top.stk
  let ini = idxNB(myinput, faili.top),
  next(pop.stk, Fstate.top, faili.top, ini, failresult.top, faili.top, failresult.top)
 else if actionState = !Fail then
  let top = top.stk
  let ini = idxNB(myinput, i.top),
  next(pop.stk, Sstate.top, i.top, ini, result.top, faili.top, failresult.top)
 else if actionState = T then
  let te = idxNB(packedTable, index.state),
  if inputi ≠ match.te then {fail}next(stk, Fstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)
  else next(stk, Sstate.te, i + 1, idxNB(myinput, i + 1), result, faili, failresult)
 else if actionState = !T then
  let te = idxNB(packedTable, index.state),
  if inputi = match.te then {fail}next(stk, Sstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)
  else next(stk, Fstate.te, i, inputi, result, faili, failresult)
 else if actionState = MatchAny then
  let te = idxNB(packedTable, index.state),
  if inputi = endMark then {fail}next(stk, Fstate.te, i, inputi, result, faili, failresult)
  else
   let reslt = result + toAttribute(result sub n.result, [inputi])
   let ini = idxNB(myinput, i + 1),
   next(stk, Sstate.te, i + 1, ini, reslt, faili, failresult)
 else if actionState = T' then
  let te = idxNB(packedTable, index.state),
  if inputi = match.te then next(stk, Sstate.te, i + 1, idxNB(myinput, i + 1), result, faili, failresult)
  else next(stk, Fstate.te, i, inputi, result, faili, failresult)
 else
  {match non Terminal}
  let te = idxNB(packedTable, index.state)
  assert action.action.te ∈ [NT, NT*] report "PROBLEM PEG:(state)"
  let newstk = push(stk, frame(Sstate.te, Fstate.te, i, result, faili, failresult)),
  let tmp = [toAttribute(result sub n.result, empty:seq.word)],
  next(newstk, nextState.action.te, i, inputi, tmp, i, tmp),
resultType.push(stk, frame(state, state, i, result, n.myinput, result)) 