Module newPretty

use PEGrules

use UTF8

use prettyAttribute

use otherseq.prettyR

use standard

use otherseq.word

use seq.word

use set.seq.word

Function %(a:attribute) seq.word %.parts.a

function %(p:prettyR) seq.word "{^(prec.p)}^(text.p)"

Export escapeformat(in:seq.word) seq.word {From prettyAttribute}

Function pretty(p:seq.word) seq.word
let r = parse(p, toAttribute."", true)
let out = text.1#parts.result.r,
if status.r ∈ "Match" then out else "Fail^(p)"

Function prettyNoChange(p:seq.word) seq.word
let r = parse(p, toAttribute."", false)
let out = text.1#parts.result.r,
if status.r ∈ "Match" then out else "Fail^(p)"

function binary2(a:attribute, b:attribute, op:seq.word) attribute
if isempty.text.1#parts.b then a else attribute(parts.a + parts.b)

function binary(a:attribute, b:attribute, op:seq.word) attribute
let tmp = if isempty.text.1#parts.a then empty:seq.prettyR else parts.a,
attribute(tmp + prettyR(-1, width.op, op) + parts.b)

function unaryMinus(change:boolean, bin:attribute) attribute
let b = if change ∧ prec.1#parts.bin ≤ 2 then removeparen.bin else bin,
attribute.prettyR(2, 1 + width1.b, "-^(text1.b)")

function unaryExp(change:boolean, kind:int, a:attribute, b:attribute) attribute
if kind = 2 then
 if hexOrDecimal?.1#text1.a ∉ "other" then
 attribute.prettyR(0, width1.a + width1.b, text1.a + "." + text1.b)
 else if change then
 funccall(change, a, b, toAttribute."")
 else attribute.prettyR(2, width1.a + width1.b, text1.a + "." + text1.b)
else
 let ce = CommentExp.a,
 attribute.
  if subseq(text1.b, 1, 2) = "<* block" then
   let c = mergelist(2, ce),
   prettyR(prec.1#parts.b, 10000, "<* block^(text1.c) /br^(text1.b << 2)")
  else 1#parts.mergelist(prec.1#parts.b, ce + parts.b)

function mergebinary(change:boolean, prec:int, a0:attribute, b:attribute) attribute
let a1 = 1#parts.a0
let a2 =
 if change ∧ prec.a1 ≤ prec ∧ 1^text.a1 ∈ ") *>" then
  let txt = if prec = 11 then removeclose.text.a1 else removeparen.text.a1,
  [prettyR(prec.a1, width.txt, txt)]
 else parts.a0,
if n.parts.b = 1 ∧ isempty.text.1#parts.b then
attribute.a2
else
 let aa =
  if prec = 1 ∧ prec.1#a2 = 1 then
  [prettyR(0, width.1#a2 + 2, "(^(text.1#a2))")]
  else a2
 for op = true, binary = "", acc = aa, e ∈ parts.b
 do
  if op then
   let t = text.e,
   next(false, if t ∈ [",", ".", "^", "#"] then t else "/sp^(t) /sp", acc)
  else
   let bb =
    if change ∧ prec.e < prec ∧ 1^text.e ∈ ") *>" then
     let txt = if binary = "," then removeclose.text.e else removeparen.text.e,
     prettyR(prec.e, width.txt, txt)
    else e,
   next(true, binary, acc + prettyR(prec, width.binary + width.bb, binary + text.bb)),
 mergelist(prec, acc)

Function sortuse(b:seq.seq.word, prefix:seq.word) seq.seq.word
let a = for a = empty:seq.seq.word, u ∈ b do a + reverse.u, a
for acc = empty:seq.seq.word, @e ∈ alphasort.toseq.asset.a do acc + (prefix + reverse.@e),
acc

function combine(change:boolean, a:seq.prettyR, b:seq.prettyR, E:attribute) attribute
if isempty.b ∧ isempty.a then
E
else if not.change then
let parts = a + b + parts.E, mergelist(if prec.1#parts = 10 then 10 else 11, parts)
else
 let tmp = removeparen.text1.E
 let e = if tmp = text1.E then 1#parts.E else prettyR(0, width.tmp, tmp),
  if not(n.b = 1 ∧ isempty.text.1#b) then
   let parts = a + if isempty.text.1^b then b >> 1 else b,
   mergelist(if prec.1^parts = 10 then 10 else 11, parts >> 1 + addcomma.1^parts + e)
  else mergelist(11, a + e)

function addcomma(p:prettyR) prettyR
for i = 0, e ∈ reverse.text.p while e ∈ "*>" do i + 1,
if subseq(text.p, n.text.p - i - 1, n.text.p - i - 1) = "}" then
p
else prettyR(
 prec.p
 , width."," + width.p
 , subseq(text.p, 1, n.text.p - i) + "," + subseq(text.p, n.text.p - i + 1, n.text.p)
)

function removeblocks(in:prettyR) prettyR
let tmp = text.in
let tmp2 = removeblock.tmp,
if n.tmp > n.tmp2 then prettyR(prec.in, width.tmp2, tmp2) else in

function mergelist(prec:int, in:seq.prettyR) attribute
if n.in = 1 then
attribute.in
else
 let tmp = text.1#in
 let tmp2 = removeblock.tmp,
  if n.tmp > n.tmp2 then
  mergelist(prec, [prettyR(prec, width.tmp2, tmp2)] + in << 1)
  else
   let t =
    for width = 0, text = "", e ∈ in
    while width < maxwidth
    do next(width + width.e, text + text.e),
    prettyR(prec, width, text),
    if width.t < maxwidth then
    attribute.t
    else
     for text = text.1#in, blockIsLast = blockIsLast.text.1#in, e ∈ in << 1
     do
      if isempty.text.e then
      next(text, blockIsLast)
      else if blockIsLast ∨ subseq(text.e, 1, 2) = "<* block" then
      next(text + text.e, blockIsLast.text.e)
      else next(text + "/br" + text.e, blockIsLast.text.e),
     attribute.prettyR(prec, 10000, addblock.text)

function IfExp(change:boolean, prefix:seq.word, R1:attribute, R2:attribute) seq.prettyR
assert n.parts.R2 = 1 report "PROBLEM"
let adjust = width.prefix + 5
let cond = if change then removeclose.R1 else R1
let thenpart = parts.if change then removeclose.R2 else R2
let Then = if 1#text.1#thenpart ∈ "-" then "/keyword then /sp" else "/keyword then",
[prettyR(0, width1.cond + adjust, prefix + text1.cond + Then)] + thenpart

function fullIfExp(
 change:boolean
 , R1:attribute
 , R2:attribute
 , R3:attribute
 , R4:attribute
) attribute
let keywordelse = if 1#text1.R4 ∈ "-" then "/keyword else /sp" else "/keyword else"
let prefix = if change then "(/keyword if" else "/keyword if"
let tmp =
 if change then
 let mid = removeclose.R4, prettyR(9, 6 + width1.mid, keywordelse + text1.mid + ")")
 else prettyR(9, 5 + width1.R4, keywordelse + text1.R4),
mergelist(9, IfExp(change, prefix, R1, R2) + parts.R3 + tmp)

function LetExp(change:boolean, a:attribute, b:attribute, c:attribute) seq.prettyR
[prettyR(
 10
 , width1.a + width1.b + width1.c + 6
 , "/keyword let^(text1.a) =
 ^(if change then let x = removeclose.text1.b, x + text1.c else text1.b + text1.c)"
)]

function AssertExp(change:boolean, a:attribute, b:attribute) seq.prettyR
{assert E report E comma?}
let assertpart = "/keyword assert^(if change then removeclose.text1.a else text1.a)"
let reportpart = "/keyword report^(if change then removeclose.text1.b else text1.b)",
if width1.a + width1.b + 16 < maxwidth then
[prettyR(0, width1.a + width1.b + 16, assertpart + reportpart)]
else [prettyR(0, width1.a + 8, assertpart), prettyR(0, width1.b + 8, reportpart)]

Function AccumExp(
 change:boolean
 , accum:attribute
 , value:attribute
 , op:seq.word
) attribute
let B = if change then removeparen.value else value,
attribute.prettyR(0, width1.accum + width1.B + 2, text1.accum + op + text1.B)

function forExp(
 accumList:attribute
 , While:attribute
 , body:attribute
 , change:boolean
) attribute
{merge accum expressions}
let accums =
 if n.parts.accumList = 1 then
 accumList
 else
  let bb = attribute(parts.accumList << 1),
  mergebinary(change, 11, attribute.1#parts.accumList, bb)
let whilepart =
 if isempty.text1.While then
 prettyR(0, 0, "")
 else
  let b = if change then removeparen.While else While,
  prettyR(0, 6 + width1.b, "/keyword while^(text1.b)")
let dopart = if change then removeclose.body else body
let totalwidth = width1.accums + width1.dopart + width.whilepart + 7,
attribute.
 if totalwidth < maxwidth then
 [prettyR(
  10
  , totalwidth
  , "/keyword for^(text1.accums + text.whilepart) /keyword do^(text1.dopart)"
 )]
 else
  attr("/keyword for", accums)
   + whilepart
   + prettyR(10, 3 + width1.dopart, "/keyword do^(text1.dopart)")

function brackets(change:boolean, prec:int, ain:attribute) attribute
let a = if change then removeparen.ain else ain,
attribute.prettyR(prec.1#parts.a, width1.a + 2, "(^(text1.a))")

function CommentExp(a:attribute) seq.prettyR
let p = 1#parts.a
let tmp =
 if width.p ≤ maxwidth then
 text.p
 else
  for w1 = 0, acc = "", w ∈ text.p
  do
   let t = n.decodeword.w + 1,
    if w ∈ "/br /p /row" then
    next(t, acc + escapeformat + "/br" + escapeformat + w)
    else if w1 + t > maxwidth then
    next(t, acc + escapeformat + "/br" + escapeformat + w)
    else next(w1 + t, acc + w),
  acc,
addBlock([prettyR(0, width.p + 2, tmp)], "comment")

function quote(all:seq.prettyR) attribute
for width2 = 0, text1 = "", text2 = "", hasbreak = 0, e ∈ all
do
 if subseq(text.e, 1, 2) = "^" + "(" then
  if width2 + width.e > maxwidth then
  next(
   width.e
   , text1 + text.e
   , text2 + "^(escapeformat) /br^(escapeformat)" + text.e
   , hasbreak
  )
  else next(width2 + width.e, text1 + text.e, text2 + text.e, hasbreak)
 else
  for partWidth = 0, partText = "", partHasbreak = 0, w ∈ text.e
  do
   let wordWidth = n.decodeword.w + 1,
    if w ∈ "/br /p /row" then
    next(wordWidth, partText + escapeformat + "/br" + escapeformat + w, 1)
    else if partWidth + wordWidth > maxwidth then
    next(wordWidth, partText + escapeformat + "/br" + escapeformat + w, 1)
    else next(partWidth + wordWidth, partText + w, partHasbreak),
  next(width2 + partWidth, text1 + text.e, text2 + partText, partHasbreak + hasbreak)
let size = width."^(escapeformat)^(text1)^(escapeformat)",
attribute.addBlock(
 [
  if size < maxwidth then
  prettyR(0, size, text1)
  else prettyR(0, if hasbreak > 0 then 10000 else width2 + 3, text2)
 ]
 , "literal"
)

function fixname(s:seq.word, a:attribute) seq.prettyR
let name = text.1#parts.a
let name1 = if 1#name ∈ "+=-^#" then s + "/sp" + name else s + name
let widthname = width.name1
let widthlast = width.1^parts.a
let textlast = if 1^s ∈ ":" then {Export type:} "" else text.1^parts.a
for text = "", width = 0, text2 = "", p ∈ subseq(parts.a, 2, n.parts.a - 1)
do next(text + text.p, width + width.p, if isempty.text.p then text2 else text2 + text.p + "/br"),
if widthname + width + widthlast < maxwidth then
[prettyR(0, widthname + width + widthlast, "/keyword^(name1)^(text)^(textlast)")]
else
 [prettyR(0, width.name1, "/keyword^(name1)")]
  + prettyR(0, 10000, addblock(text2 >> 1))
  + 1^parts.a

function start(s:seq.word, a:attribute, b:attribute) attribute
let tmp = if s = "type" then parts.toAttribute."/keyword type^(text1.a) is" else fixname(s, a),
toAttribute.removeblock.text1.mergelist(11, tmp + parts.b)

function start(
 change:boolean
 , s:seq.word
 , a:attribute
 , b:attribute
 , c:attribute
) attribute
let txt = removeclose.removeblock.removeparen.text1.c
let newc = if txt = text1.c then 1#parts.c else prettyR(0, width.txt, txt),
toAttribute.removeblock.text1.combine(change, fixname(s, a), parts.b, attribute.newc)

function addBlock(s:seq.prettyR, kind:seq.word) seq.prettyR
let fixes =
 if kind = "literal" then
 ["<* literal /tag^(dq)^(escapeformat)", "^(escapeformat)^(dq) *>"]
 else ["<* comment^(escapeformat) {", "}^(escapeformat) *>"],
if n.s = 1 then
[prettyR(0, width.1#s, 1#fixes + text.1#s + 2#fixes)]
else [prettyR(0, 0, 1#fixes)] + s + prettyR(0, 0, 2#fixes)

function slash word 1#"/"

function %(b:boolean) seq.word if b then "true" else "false"

function promoteFirstLineOfBLock(s:seq.word) seq.word
{does it work for" a"+" b
/br c"}
for kk = 0, inescape = false, nesting = 0, continue = true, hasbreak = false, last = 1#"?", w ∈ s
while continue
do
 if last = escapeformat then
 next(kk + 1, not.inescape, nesting, true, hasbreak, w)
 else if inescape then
 next(kk + 1, inescape, nesting, true, hasbreak, w)
 else if last ∈ "<*" then
 next(kk + 1, inescape, nesting + 1, true, hasbreak, w)
 else if last ∈ "*>" then
 next(kk + 1, inescape, nesting - 1, true, hasbreak, w)
 else if last ∈ "/br" then
 next(kk + 1, inescape, nesting, nesting > 0, true, w)
 else next(kk + 1, inescape, nesting, true, hasbreak, w),
if (kk - 1)#s ∈ "/br" then
subseq(s, 1, kk - 2) + "<* block" + s << (kk - 1)
else "<* block^(s)"

function funccall(change:boolean, name:attribute, b:attribute, c:attribute) attribute
let a = 1#parts.b
let aa =
 if change ∧ 1^text.a ∈ ") *>" then
 let txt = removeclose.text.a, prettyR(prec.a, width.a + n.txt - n.text.a, txt)
 else a,
attribute.
 if n.parts.c = 1 ∧ isempty.text1.c then
  if n.parts.name = 0 then
  prettyR(0, width.aa + 4, "[^(text.aa)]")
  else if change ∧ n.text1.name = 1 ∧ prec.aa ≤ 2 then
  let new = "^(text1.name).^(text.aa)", prettyR(2, width.new, new)
  else if change ∧ prec.aa = 9 then
  prettyR(9, width1.name + 1 + width.aa, "(^(text1.name).^(text.aa))")
  else prettyR(0, width1.name + 2 + width.aa, "^(text1.name) /tag (^(text.aa))")
 else
  let aa1 = removeblocks.aa
  for
   op = true
   , acc = text.aa1
   , blockacc = text.aa1
   , flag = blockIsLast.text.aa1
   , width = width.aa1
   , e ∈ parts.c
  do
   if op then
   next(false, acc, blockacc, flag, width)
   else
    let bb0 =
     if change ∧ 1^text.e ∈ ") *>" then
     let txt = removeclose.text.e, prettyR(prec.e, width.txt, txt)
     else e
    let bb = if prec.e ≠ 10 then bb0 else prettyR(prec.e, width.bb0 + 2, "(^(text.bb0))")
    let textbb =
     if subseq(text.bb, 1, 2) = "<* block" then
     promoteFirstLineOfBLock(text.bb << 2)
     else text.bb
    let newblockacc = blockacc + if flag then ",^(textbb)" else "/br,^(textbb)",
    next(
     true
     , acc + "," + textbb
     , newblockacc
     , blockIsLast.textbb
     , width + width."," + width.bb
    ),
   if n.parts.name = 0 then
    let totalwidth = width + 4,
     if width < maxwidth then
     prettyR(0, totalwidth, "[^(acc)]")
     else prettyR(0, 10000, "[^(addblock.blockacc)]")
   else
    let totalwidth = width + width1.name + 2,
     if width < maxwidth then
     prettyR(0, totalwidth, "^(text1.name) /tag (^(acc))")
     else prettyR(0, totalwidth, "^(text1.name) /tag (^(addblock.blockacc))")

function endMark word encodeword.[char.254]

function PEGgen(
 seqElementType:word
 , attributeType:attribute
 , resultType:runresult
 , R:seq.attribute
 , common:boolean
 , commonType:boolean
) seq.boolean
{commonName = common wordmap = carrot 1#"^", slash slash, dq 1#dq, 1#" $"}
[
 "Pretty function Header Declare' E" = start(common, "function", $.1, $.2, $.3)
 , "/ Function Header Declare' E" = start(common, "Function", $.1, $.2, $.3)
 , "/ type Id is FPL Comment" = start("type", $.1, attribute(parts.$.2 + parts.$.3))
 , "/ Export type:Type Comment" = start("Export type:", $.1, $.2)
 , "/ Export Header Comment" = start("Export", $.1, $.2)
 , "/ Builtin Header Comment" = start("Builtin", $.1, $.2)
 , "/ builtin Header Comment" = start("builtin", $.1, $.2)
 , "/ unbound Header Comment" = start("unbound", $.1, $.2)
 , "Header Name (FPL) Type"
  = attribute(prettyR(text1.$.1 + "/tag (") + parts.$.2 + prettyR.")^(text1.$.3)")
 , "/ Name Type" = attribute(parts.$.1 + parts.$.2)
 , "* Comment {N}" = attribute(parts.$.0 + CommentExp.$.1)
 , "String dq String' dq" = quote.parts.$.1
 , "* String' carrot (E)"
  = attribute(
   parts.$.0
    + prettyR(
    0
    , width1.$.1 + 4
    , "^" + "(^(escapeformat)^(removeparen.text1.$.1)^(escapeformat))"
   )
  )
 , "/ carrot" = attribute(parts.$.0 + prettyR."^")
 , "/ str2" = attribute(parts.$.0 + parts.$.1)
 , "+str2 ! dq ! carrot any" = /All
 , "E Or" = $.1
 , "* EL', E" = binary($.0, $.1, ",")
 , "Or And Or'" = mergebinary(common, 8, $.1, $.2)
 , "* Or' ∨ And" = binary($.0, $.1, "∨")
 , "/ /or And" = binary($.0, $.1, "∨")
 , "/ ⊻ And" = binary($.0, $.1, "⊻")
 , "And Compare And'" = mergebinary(common, 7, $.1, $.2)
 , "* And' ∧ Compare" = binary($.0, $.1, "∧")
 , "/ /and Compare" = binary($.0, $.1, "∧")
 , "Compare Sum Compare'" = mergebinary(common, 6, $.1, $.2)
 , "* Compare' = Sum" = binary($.0, $.1, "=")
 , "/ ≠ Sum" = binary($.0, $.1, "≠")
 , "/ > Sum" = binary($.0, $.1, ">")
 , "/ < Sum" = binary($.0, $.1, "<")
 , "/ >1 Sum" = binary($.0, $.1, ">1")
 , "/ >2 Sum" = binary($.0, $.1, ">2")
 , "/ ≥ Sum" = binary($.0, $.1, "≥")
 , "/ /ge Sum" = binary($.0, $.1, "≥")
 , "/ ≤ Sum" = binary($.0, $.1, "≤")
 , "/ /le Sum" = binary($.0, $.1, "≤")
 , "/ /ne Sum" = binary($.0, $.1, "≠")
 , "Sum Product Sum'" = mergebinary(common, 4, $.1, $.2)
 , "* Sum'-Product" = binary($.0, $.1, "-")
 , "/+Product" = binary($.0, $.1, "+")
 , "/ ∈ Product" = binary($.0, $.1, "∈")
 , "/ /in Product" = binary($.0, $.1, "∈")
 , "/ ∉ Product" = binary($.0, $.1, "∉")
 , "/ /nin Product" = binary($.0, $.1, "∉")
 , "Product Unary Product'" = mergebinary(common, 3, $.1, $.2)
 , "* Product' * Unary" = binary($.0, $.1, "*")
 , "/ >> Unary" = binary($.0, $.1, ">>")
 , "/ << Unary" = binary($.0, $.1, "<<")
 , "/ slash Unary" = binary($.0, $.1, [slash])
 , "/ mod Unary" = binary($.0, $.1, "mod")
 , "/ ∩ Unary" = binary($.0, $.1, "∩")
 , "/ ∪ Unary" = binary($.0, $.1, "∪")
 , "/ /cap Unary" = binary($.0, $.1, "∩")
 , "/ /cup Unary" = binary($.0, $.1, "∪")
 , "/ \ Unary" = binary($.0, $.1, "\")
 , "Unary-Unary" = unaryMinus(common, $.1)
 , "/ Id.Unary" = unaryExp(common, 2, $.1, $.2)
 , "/ {N} Unary" = unaryExp(common, 3, $.1, $.2)
 , "/ Power" = $.1
 , "Power Atom Power'" = mergebinary(common, 1, $.1, $.2)
 , "* Power'#Unary" = binary($.0, $.1, "#")
 , "/^Unary" = binary($.0, $.1, "^")
 , "Atom (E)"
  = 
   let a = if common then removeparen.$.1 else $.1,
   attribute.prettyR(prec.1#parts.a, width1.a + 2, "(^(text1.a))")
 , "/ [E EL']" = funccall(common, attribute.empty:seq.prettyR, $.1, $.2)
 , "/ String" = $.1
 , "/ Declare Declare' E" = combine(common, empty:seq.prettyR, parts.$.1 + parts.$.2, $.3)
 , "/ if E then E IF else E" = fullIfExp(common, $.1, $.2, $.3, $.4)
 , "/ Name (E EL')" = funccall(common, $.1, $.2, $.3)
 , "/ Name" = $.1
 , "Name Id:Type"
  = attribute.prettyR(0, width1.$.1 + 2 + width1.$.2, text1.$.1 + ":" + text1.$.2)
 , "/ Id" = $.1
 , "Id !, !] !) !:!.! dq any" = $.1
 , "comma?," = (toAttribute.if common then "" else ",")
 , "/" = toAttribute.""
 , "* IF else if E then E"
  = attribute(parts.$.0 + IfExp(common, "/keyword else /keyword if", $.1, $.2))
 , "Type Id.Type"
  = attribute.prettyR(0, width1.$.1 + width1.$.2, text1.$.1 + "." + text1.$.2)
 , "/ Id" = $.1
 , "Declare let any = E comma?" = attribute.LetExp(common, $.1, $.2, $.3)
 , "/ assert E report E comma?" = attribute.AssertExp(common, $.1, $.2)
 , "/ {N} comma?" = attribute.CommentExp.$.1
 , "/ for ForDeclare do E comma?" = forExp($.1, toAttribute."", $.2, common)
 , "/ for ForDeclare while E do E comma?" = forExp($.1, $.2, $.3, common)
 , "ForDeclare AccumList, any ∈ E" = binary($.1, AccumExp(common, $.2, $.3, "∈"), ",")
 , "/ AccumList, any /in E" = binary($.1, AccumExp(common, $.2, $.3, "∈"), ",")
 , "/ AccumList" = $.1
 , "AccumList ! while any = E AccumList'"
  = 
   let accum = AccumExp(common, $.1, $.2, "="),
   if isempty.text.1#parts.$.3 then accum else attribute(parts.accum + parts.$.3)
 , "* AccumList', any = E" = binary($.0, AccumExp(common, $.1, $.2, "="), ",")
 , "* Declare' Declare" = attribute(parts.$.0 + parts.$.1)
 , "FPL FP FPL'" = attribute(parts.$.1 + parts.$.2)
 , "* FPL', FP" = attribute(parts.$.0 + prettyR.",^(text1.$.1)")
 , "FP any:Type"
  = attribute.prettyR(0, width1.$.1 + 1 + width1.$.2 + 1, text1.$.1 + ":" + text1.$.2)
 , "/ Type" = $.1
 , "* N {N}" = /All
 , "/ !} any" = /All
]

<<<< Below is auto generated code >>>>

/br Non-terminals:AccumList AccumList' And And' Atom Comment Compare Compare' Declare Declare' E
EL' FP FPL FPL' ForDeclare Header IF Id N Name Or Or' Power Power' Pretty Product Product' String String'
Sum Sum' Type Unary comma? str2
/br Terminals:#() *+,-./and /cap /cup /ge /in /le /ne /nin /or:< << = > >1 >2 >> Builtin Export
Function [\]^any assert builtin carrot do dq else for function if is let mod report slash then type
unbound while {} ∈ ∉ ∧ ∨ ∩ ∪ ≠ ≤ ≥ ⊻
/br Pretty ← function Header Declare' E / Function Header Declare' E / type Id is FPL Comment / Export
type:Type Comment / Export Header Comment / Builtin Header Comment / builtin Header Comment / unbound
Header Comment
/br Header ← Name (FPL) Type / Name Type
/br * Comment ← {N}
/br String ← dq String' dq
/br * String' ← carrot (E) / carrot / str2
/br+str2 ← ! dq ! carrot any
/br E ← Or
/br * EL' ←, E
/br Or ← And Or'
/br * Or' ← ∨ And / /or And / ⊻ And
/br And ← Compare And'
/br * And' ← ∧ Compare / /and Compare
/br Compare ← Sum Compare'
/br * Compare' ← = Sum / ≠ Sum / > Sum / < Sum / >1 Sum / >2 Sum / ≥ Sum / /ge Sum / ≤ Sum / /le Sum
/ /ne Sum
/br Sum ← Product Sum'
/br * Sum' ←-Product /+Product / ∈ Product / /in Product / ∉ Product / /nin Product
/br Product ← Unary Product'
/br * Product' ← * Unary / >> Unary / << Unary / slash Unary / mod Unary / ∩ Unary / ∪ Unary / /cap Unary
/ /cup Unary / \ Unary
/br Unary ←-Unary / Id.Unary / {N} Unary / Power
/br Power ← Atom Power'
/br * Power' ←#Unary /^Unary
/br Atom ← (E) / [E EL'] / String / Declare Declare' E / if E then E IF else E / Name (E EL') / Name
/br Name ← Id:Type / Id
/br Id ← !, !] !) !:!.! dq any
/br comma? ←, /
/br * IF ← else if E then E
/br Type ← Id.Type / Id
/br Declare ← let any = E comma? / assert E report E comma? / {N} comma? / for ForDeclare do E comma?
/ for ForDeclare while E do E comma?
/br ForDeclare ← AccumList, any ∈ E / AccumList, any /in E / AccumList
/br AccumList ← ! while any = E AccumList'
/br * AccumList' ←, any = E
/br * Declare' ← Declare
/br FPL ← FP FPL'
/br * FPL' ←, FP
/br FP ← any:Type / Type
/br * N ← {N} / !} any

function action(partno:int, R:seq.attribute, common:boolean) attribute
if partno = 2 then
start(common, "function", 3^R, 2^R, 1^R)
else if partno = 3 then
start(common, "Function", 3^R, 2^R, 1^R)
else if partno = 4 then
start("type", 3^R, attribute(parts.2^R + parts.1^R))
else if partno = 5 then
start("Export type:", 2^R, 1^R)
else if partno = 6 then
start("Export", 2^R, 1^R)
else if partno = 7 then
start("Builtin", 2^R, 1^R)
else if partno = 8 then
start("builtin", 2^R, 1^R)
else if partno = 9 then
start("unbound", 2^R, 1^R)
else if partno = 10 then
attribute(prettyR(text1.3^R + "/tag (") + parts.2^R + prettyR.")^(text1.1^R)")
else if partno = 11 then
attribute(parts.2^R + parts.1^R)
else if partno = 12 then
attribute(parts.2^R + CommentExp.1^R)
else if partno = 13 then
quote.parts.1^R
else if partno = 14 then
attribute(
 parts.2^R
  + prettyR(
  0
  , width1.1^R + 4
  , "^" + "(^(escapeformat)^(removeparen.text1.1^R)^(escapeformat))"
 )
)
else if partno = 15 then
attribute(parts.1^R + prettyR."^")
else if partno = 16 then
attribute(parts.2^R + parts.1^R)
else if partno = 18 then
1^R
else if partno = 19 then
binary(2^R, 1^R, ",")
else if partno = 20 then
mergebinary(common, 8, 2^R, 1^R)
else if partno = 21 then
binary(2^R, 1^R, "∨")
else if partno = 22 then
binary(2^R, 1^R, "∨")
else if partno = 23 then
binary(2^R, 1^R, "⊻")
else if partno = 24 then
mergebinary(common, 7, 2^R, 1^R)
else if partno = 25 then
binary(2^R, 1^R, "∧")
else if partno = 26 then
binary(2^R, 1^R, "∧")
else if partno = 27 then
mergebinary(common, 6, 2^R, 1^R)
else if partno = 28 then
binary(2^R, 1^R, "=")
else if partno = 29 then
binary(2^R, 1^R, "≠")
else if partno = 30 then
binary(2^R, 1^R, ">")
else if partno = 31 then
binary(2^R, 1^R, "<")
else if partno = 32 then
binary(2^R, 1^R, ">1")
else if partno = 33 then
binary(2^R, 1^R, ">2")
else if partno = 34 then
binary(2^R, 1^R, "≥")
else if partno = 35 then
binary(2^R, 1^R, "≥")
else if partno = 36 then
binary(2^R, 1^R, "≤")
else if partno = 37 then
binary(2^R, 1^R, "≤")
else if partno = 38 then
binary(2^R, 1^R, "≠")
else if partno = 39 then
mergebinary(common, 4, 2^R, 1^R)
else if partno = 40 then
binary(2^R, 1^R, "-")
else if partno = 41 then
binary(2^R, 1^R, "+")
else if partno = 42 then
binary(2^R, 1^R, "∈")
else if partno = 43 then
binary(2^R, 1^R, "∈")
else if partno = 44 then
binary(2^R, 1^R, "∉")
else if partno = 45 then
binary(2^R, 1^R, "∉")
else if partno = 46 then
mergebinary(common, 3, 2^R, 1^R)
else if partno = 47 then
binary(2^R, 1^R, "*")
else if partno = 48 then
binary(2^R, 1^R, ">>")
else if partno = 49 then
binary(2^R, 1^R, "<<")
else if partno = 50 then
binary(2^R, 1^R, [slash])
else if partno = 51 then
binary(2^R, 1^R, "mod")
else if partno = 52 then
binary(2^R, 1^R, "∩")
else if partno = 53 then
binary(2^R, 1^R, "∪")
else if partno = 54 then
binary(2^R, 1^R, "∩")
else if partno = 55 then
binary(2^R, 1^R, "∪")
else if partno = 56 then
binary(2^R, 1^R, "\")
else if partno = 57 then
unaryMinus(common, 1^R)
else if partno = 58 then
unaryExp(common, 2, 2^R, 1^R)
else if partno = 59 then
unaryExp(common, 3, 2^R, 1^R)
else if partno = 60 then
1^R
else if partno = 61 then
mergebinary(common, 1, 2^R, 1^R)
else if partno = 62 then
binary(2^R, 1^R, "#")
else if partno = 63 then
binary(2^R, 1^R, "^")
else if partno = 64 then
 let a = if common then removeparen.1^R else 1^R,
 attribute.prettyR(prec.1#parts.a, width1.a + 2, "(^(text1.a))")
else if partno = 65 then
funccall(common, attribute.empty:seq.prettyR, 2^R, 1^R)
else if partno = 66 then
1^R
else if partno = 67 then
combine(common, empty:seq.prettyR, parts.3^R + parts.2^R, 1^R)
else if partno = 68 then
fullIfExp(common, 4^R, 3^R, 2^R, 1^R)
else if partno = 69 then
funccall(common, 3^R, 2^R, 1^R)
else if partno = 70 then
1^R
else if partno = 71 then
attribute.prettyR(0, width1.2^R + 2 + width1.1^R, text1.2^R + ":" + text1.1^R)
else if partno = 72 then
1^R
else if partno = 73 then
1^R
else if partno = 74 then
toAttribute.if common then "" else ","
else if partno = 75 then
toAttribute.""
else if partno = 76 then
attribute(parts.3^R + IfExp(common, "/keyword else /keyword if", 2^R, 1^R))
else if partno = 77 then
attribute.prettyR(0, width1.2^R + width1.1^R, text1.2^R + "." + text1.1^R)
else if partno = 78 then
1^R
else if partno = 79 then
attribute.LetExp(common, 3^R, 2^R, 1^R)
else if partno = 80 then
attribute.AssertExp(common, 3^R, 2^R)
else if partno = 81 then
attribute.CommentExp.2^R
else if partno = 82 then
forExp(3^R, toAttribute."", 2^R, common)
else if partno = 83 then
forExp(4^R, 3^R, 2^R, common)
else if partno = 84 then
binary(3^R, AccumExp(common, 2^R, 1^R, "∈"), ",")
else if partno = 85 then
binary(3^R, AccumExp(common, 2^R, 1^R, "∈"), ",")
else if partno = 86 then
1^R
else if partno = 87 then
 let accum = AccumExp(common, 3^R, 2^R, "="),
 if isempty.text.1#parts.1^R then accum else attribute(parts.accum + parts.1^R)
else if partno = 88 then
binary(3^R, AccumExp(common, 2^R, 1^R, "="), ",")
else if partno = 89 then
attribute(parts.2^R + parts.1^R)
else if partno = 90 then
attribute(parts.2^R + parts.1^R)
else if partno = 91 then
attribute(parts.2^R + prettyR.",^(text1.1^R)")
else if partno = 92 then
attribute.prettyR(0, width1.2^R + 1 + width1.1^R + 1, text1.2^R + ":" + text1.1^R)
else if partno = 93 then
1^R
else 1#R

function mytable seq.tableEntry
[
 {1} tableEntry(NT.T'.2, 1#"?", Match, Failure, "")
 , {2} tableEntry(T', 1#"function", NT.3, T'.6, "")
 , {3} tableEntry(NT.32, 1#"Header", NT.4, T'.6, "")
 , {4} tableEntry(NT.238, 1#"Declare'", NT.5, T'.6, "")
 , {5} tableEntry(NT.54, 1#"E", Reduce.2, T'.6, "")
 , {6} tableEntry(T', 1#"Function", NT.7, T'.10, "")
 , {7} tableEntry(NT.32, 1#"Header", NT.8, T'.10, "")
 , {8} tableEntry(NT.238, 1#"Declare'", NT.9, T'.10, "")
 , {9} tableEntry(NT.54, 1#"E", Reduce.3, T'.10, "")
 , {10} tableEntry(T', 1#"type", NT.11, T'.15, "")
 , {11} tableEntry(NT.!T.175, 1#"Id", T.12, T'.15, "")
 , {12} tableEntry(T, 1#"is", NT.13, T'.15, "")
 , {13} tableEntry(NT.239, 1#"FPL", NT.14, T'.15, "")
 , {14} tableEntry(NT.T.39, 1#"Comment", Reduce.4, T'.15, "")
 , {15} tableEntry(T', 1#"Export", T'.16, T'.23, "")
 , {16} tableEntry(T', 1#"type", T.17, NT.21, "")
 , {17} tableEntry(T, 1#":", NT.18, T'.20, "")
 , {18} tableEntry(NT.188, 1#"Type", NT.19, T'.20, "")
 , {19} tableEntry(NT.T.39, 1#"Comment", Reduce.5, T'.20, "")
 , {20} tableEntry(T', 1#"Export", NT.21, T'.23, "")
 , {21} tableEntry(NT.32, 1#"Header", NT.22, T'.23, "")
 , {22} tableEntry(NT.T.39, 1#"Comment", Reduce.6, T'.23, "")
 , {23} tableEntry(T', 1#"Builtin", NT.24, T'.26, "")
 , {24} tableEntry(NT.32, 1#"Header", NT.25, T'.26, "")
 , {25} tableEntry(NT.T.39, 1#"Comment", Reduce.7, T'.26, "")
 , {26} tableEntry(T', 1#"builtin", NT.27, T.29, "")
 , {27} tableEntry(NT.32, 1#"Header", NT.28, T.29, "")
 , {28} tableEntry(NT.T.39, 1#"Comment", Reduce.8, T.29, "")
 , {29} tableEntry(T, 1#"unbound", NT.30, Fail, "")
 , {30} tableEntry(NT.32, 1#"Header", NT.31, Fail, "")
 , {31} tableEntry(NT.T.39, 1#"Comment", Reduce.9, Fail, "")
 , {32} tableEntry(NT.171, 1#"Name", T'.33, Fail, "")
 , {33} tableEntry(T', 1#"(", NT.34, NT.38, "")
 , {34} tableEntry(NT.239, 1#"FPL", T.35, NT.37, "")
 , {35} tableEntry(T, 1#")", NT.36, NT.37, "")
 , {36} tableEntry(NT.188, 1#"Type", Reduce.10, NT.37, "")
 , {37} tableEntry(NT.171, 1#"Name", NT.38, Fail, "")
 , {38} tableEntry(NT.188, 1#"Type", Reduce.11, Fail, "")
 , {39} tableEntry(T, 1#"{", NT.40, Success*, "")
 , {40} tableEntry(NT.T.247, 1#"N", T.41, Success*, "")
 , {41} tableEntry(T, 1#"}", Reduce*(12, T.39), Success*, "")
 , {42} tableEntry(T, 1#dq, NT.43, Fail, "")
 , {43} tableEntry(NT.T'.45, 1#"String'", T.44, Fail, "")
 , {44} tableEntry(T, 1#dq, Reduce.13, Fail, "")
 , {45} tableEntry(T', 1#"^", T.46, NT.50, "")
 , {46} tableEntry(T, 1#"(", NT.47, T'.49, "")
 , {47} tableEntry(NT.54, 1#"E", T.48, T'.49, "")
 , {48} tableEntry(T, 1#")", Reduce*(14, T'.45), T'.49, "")
 , {49} tableEntry(T', 1#"^", Reduce*(15, T'.45), NT.50, "")
 , {50} tableEntry(NT.!T.51, 1#"str2", Reduce*(16, T'.45), Success*, "")
 , {51} tableEntry(!T, 1#dq, Fail, !T.52, "")
 , {52} tableEntry(!T, 1#"^", Fail, MatchAny.53, "")
 , {53} tableEntry(MatchAny, 1#"?", Discard*.!T.252, Fail, "")
 , {54} tableEntry(NT.57, 1#"Or", Reduce.18, Fail, "")
 , {55} tableEntry(T, 1#",", NT.56, Success*, "")
 , {56} tableEntry(NT.54, 1#"E", Reduce*(19, T.55), Success*, "")
 , {57} tableEntry(NT.65, 1#"And", NT.58, Fail, "")
 , {58} tableEntry(NT.T'.59, 1#"Or'", Reduce.20, Fail, "")
 , {59} tableEntry(T', 1#"∨", NT.60, T'.61, "")
 , {60} tableEntry(NT.65, 1#"And", Reduce*(21, T'.59), T'.61, "")
 , {61} tableEntry(T', 1#"/or", NT.62, T.63, "")
 , {62} tableEntry(NT.65, 1#"And", Reduce*(22, T'.59), T.63, "")
 , {63} tableEntry(T, 1#"⊻", NT.64, Success*, "")
 , {64} tableEntry(NT.65, 1#"And", Reduce*(23, T'.59), Success*, "")
 , {65} tableEntry(NT.71, 1#"Compare", NT.66, Fail, "")
 , {66} tableEntry(NT.T'.67, 1#"And'", Reduce.24, Fail, "")
 , {67} tableEntry(T', 1#"∧", NT.68, T.69, "")
 , {68} tableEntry(NT.71, 1#"Compare", Reduce*(25, T'.67), T.69, "")
 , {69} tableEntry(T, 1#"/and", NT.70, Success*, "")
 , {70} tableEntry(NT.71, 1#"Compare", Reduce*(26, T'.67), Success*, "")
 , {71} tableEntry(NT.95, 1#"Sum", NT.72, Fail, "")
 , {72} tableEntry(NT.T'.73, 1#"Compare'", Reduce.27, Fail, "")
 , {73} tableEntry(T', 1#"=", NT.74, T'.75, "")
 , {74} tableEntry(NT.95, 1#"Sum", Reduce*(28, T'.73), T'.75, "")
 , {75} tableEntry(T', 1#"≠", NT.76, T'.77, "")
 , {76} tableEntry(NT.95, 1#"Sum", Reduce*(29, T'.73), T'.77, "")
 , {77} tableEntry(T', 1#">", NT.78, T'.79, "")
 , {78} tableEntry(NT.95, 1#"Sum", Reduce*(30, T'.73), T'.79, "")
 , {79} tableEntry(T', 1#"<", NT.80, T'.81, "")
 , {80} tableEntry(NT.95, 1#"Sum", Reduce*(31, T'.73), T'.81, "")
 , {81} tableEntry(T', 1#">1", NT.82, T'.83, "")
 , {82} tableEntry(NT.95, 1#"Sum", Reduce*(32, T'.73), T'.83, "")
 , {83} tableEntry(T', 1#">2", NT.84, T'.85, "")
 , {84} tableEntry(NT.95, 1#"Sum", Reduce*(33, T'.73), T'.85, "")
 , {85} tableEntry(T', 1#"≥", NT.86, T'.87, "")
 , {86} tableEntry(NT.95, 1#"Sum", Reduce*(34, T'.73), T'.87, "")
 , {87} tableEntry(T', 1#"/ge", NT.88, T'.89, "")
 , {88} tableEntry(NT.95, 1#"Sum", Reduce*(35, T'.73), T'.89, "")
 , {89} tableEntry(T', 1#"≤", NT.90, T'.91, "")
 , {90} tableEntry(NT.95, 1#"Sum", Reduce*(36, T'.73), T'.91, "")
 , {91} tableEntry(T', 1#"/le", NT.92, T.93, "")
 , {92} tableEntry(NT.95, 1#"Sum", Reduce*(37, T'.73), T.93, "")
 , {93} tableEntry(T, 1#"/ne", NT.94, Success*, "")
 , {94} tableEntry(NT.95, 1#"Sum", Reduce*(38, T'.73), Success*, "")
 , {95} tableEntry(NT.109, 1#"Product", NT.96, Fail, "")
 , {96} tableEntry(NT.T'.97, 1#"Sum'", Reduce.39, Fail, "")
 , {97} tableEntry(T', 1#"-", NT.98, T'.99, "")
 , {98} tableEntry(NT.109, 1#"Product", Reduce*(40, T'.97), T'.99, "")
 , {99} tableEntry(T', 1#"+", NT.100, T'.101, "")
 , {100} tableEntry(NT.109, 1#"Product", Reduce*(41, T'.97), T'.101, "")
 , {101} tableEntry(T', 1#"∈", NT.102, T'.103, "")
 , {102} tableEntry(NT.109, 1#"Product", Reduce*(42, T'.97), T'.103, "")
 , {103} tableEntry(T', 1#"/in", NT.104, T'.105, "")
 , {104} tableEntry(NT.109, 1#"Product", Reduce*(43, T'.97), T'.105, "")
 , {105} tableEntry(T', 1#"∉", NT.106, T.107, "")
 , {106} tableEntry(NT.109, 1#"Product", Reduce*(44, T'.97), T.107, "")
 , {107} tableEntry(T, 1#"/nin", NT.108, Success*, "")
 , {108} tableEntry(NT.109, 1#"Product", Reduce*(45, T'.97), Success*, "")
 , {109} tableEntry(NT.T'.131, 1#"Unary", NT.110, Fail, "")
 , {110} tableEntry(NT.T'.111, 1#"Product'", Reduce.46, Fail, "")
 , {111} tableEntry(T', 1#"*", NT.112, T'.113, "")
 , {112} tableEntry(NT.T'.131, 1#"Unary", Reduce*(47, T'.111), T'.113, "")
 , {113} tableEntry(T', 1#">>", NT.114, T'.115, "")
 , {114} tableEntry(NT.T'.131, 1#"Unary", Reduce*(48, T'.111), T'.115, "")
 , {115} tableEntry(T', 1#"<<", NT.116, T'.117, "")
 , {116} tableEntry(NT.T'.131, 1#"Unary", Reduce*(49, T'.111), T'.117, "")
 , {117} tableEntry(T', slash, NT.118, T'.119, "")
 , {118} tableEntry(NT.T'.131, 1#"Unary", Reduce*(50, T'.111), T'.119, "")
 , {119} tableEntry(T', 1#"mod", NT.120, T'.121, "")
 , {120} tableEntry(NT.T'.131, 1#"Unary", Reduce*(51, T'.111), T'.121, "")
 , {121} tableEntry(T', 1#"∩", NT.122, T'.123, "")
 , {122} tableEntry(NT.T'.131, 1#"Unary", Reduce*(52, T'.111), T'.123, "")
 , {123} tableEntry(T', 1#"∪", NT.124, T'.125, "")
 , {124} tableEntry(NT.T'.131, 1#"Unary", Reduce*(53, T'.111), T'.125, "")
 , {125} tableEntry(T', 1#"/cap", NT.126, T'.127, "")
 , {126} tableEntry(NT.T'.131, 1#"Unary", Reduce*(54, T'.111), T'.127, "")
 , {127} tableEntry(T', 1#"/cup", NT.128, T.129, "")
 , {128} tableEntry(NT.T'.131, 1#"Unary", Reduce*(55, T'.111), T.129, "")
 , {129} tableEntry(T, 1#"\", NT.130, Success*, "")
 , {130} tableEntry(NT.T'.131, 1#"Unary", Reduce*(56, T'.111), Success*, "")
 , {131} tableEntry(T', 1#"-", NT.132, NT.133, "")
 , {132} tableEntry(NT.T'.131, 1#"Unary", Reduce.57, NT.133, "")
 , {133} tableEntry(NT.!T.175, 1#"Id", T.134, T'.136, "")
 , {134} tableEntry(T, 1#".", NT.135, T'.136, "")
 , {135} tableEntry(NT.T'.131, 1#"Unary", Reduce.58, T'.136, "")
 , {136} tableEntry(T', 1#"{", NT.137, NT.140, "")
 , {137} tableEntry(NT.T.247, 1#"N", T.138, NT.140, "")
 , {138} tableEntry(T, 1#"}", NT.139, NT.140, "")
 , {139} tableEntry(NT.T'.131, 1#"Unary", Reduce.59, NT.140, "")
 , {140} tableEntry(NT.141, 1#"Power", Reduce.60, Fail, "")
 , {141} tableEntry(NT.T'.147, 1#"Atom", NT.142, Fail, "")
 , {142} tableEntry(NT.T'.143, 1#"Power'", Reduce.61, Fail, "")
 , {143} tableEntry(T', 1#"#", NT.144, T.145, "")
 , {144} tableEntry(NT.T'.131, 1#"Unary", Reduce*(62, T'.143), T.145, "")
 , {145} tableEntry(T, 1#"^", NT.146, Success*, "")
 , {146} tableEntry(NT.T'.131, 1#"Unary", Reduce*(63, T'.143), Success*, "")
 , {147} tableEntry(T', 1#"(", NT.148, T'.150, "")
 , {148} tableEntry(NT.54, 1#"E", T.149, T'.150, "")
 , {149} tableEntry(T, 1#")", Reduce.64, T'.150, "")
 , {150} tableEntry(T', 1#"[", NT.151, NT.154, "")
 , {151} tableEntry(NT.54, 1#"E", NT.152, NT.154, "")
 , {152} tableEntry(NT.T.55, 1#"EL'", T.153, NT.154, "")
 , {153} tableEntry(T, 1#"]", Reduce.65, NT.154, "")
 , {154} tableEntry(NT.T.42, 1#"String", Reduce.66, NT.155, "")
 , {155} tableEntry(NT.T'.192, 1#"Declare", NT.156, T'.158, "")
 , {156} tableEntry(NT.238, 1#"Declare'", NT.157, T'.158, "")
 , {157} tableEntry(NT.54, 1#"E", Reduce.67, T'.158, "")
 , {158} tableEntry(T', 1#"if", NT.159, NT.165, "")
 , {159} tableEntry(NT.54, 1#"E", T.160, NT.165, "")
 , {160} tableEntry(T, 1#"then", NT.161, NT.165, "")
 , {161} tableEntry(NT.54, 1#"E", NT.162, NT.165, "")
 , {162} tableEntry(NT.T.183, 1#"IF", T.163, NT.165, "")
 , {163} tableEntry(T, 1#"else", NT.164, NT.165, "")
 , {164} tableEntry(NT.54, 1#"E", Reduce.68, NT.165, "")
 , {165} tableEntry(NT.171, 1#"Name", T.166, Fail, "")
 , {166} tableEntry(T, 1#"(", NT.167, NT.170, "")
 , {167} tableEntry(NT.54, 1#"E", NT.168, NT.170, "")
 , {168} tableEntry(NT.T.55, 1#"EL'", T.169, NT.170, "")
 , {169} tableEntry(T, 1#")", Reduce.69, NT.170, "")
 , {170} tableEntry(NT.171, 1#"Name", Reduce.70, Fail, "")
 , {171} tableEntry(NT.!T.175, 1#"Id", T.172, Fail, "")
 , {172} tableEntry(T, 1#":", NT.173, NT.174, "")
 , {173} tableEntry(NT.188, 1#"Type", Reduce.71, NT.174, "")
 , {174} tableEntry(NT.!T.175, 1#"Id", Reduce.72, Fail, "")
 , {175} tableEntry(!T, 1#",", Fail, !T.176, "")
 , {176} tableEntry(!T, 1#"]", Fail, !T.177, "")
 , {177} tableEntry(!T, 1#")", Fail, !T.178, "")
 , {178} tableEntry(!T, 1#":", Fail, !T.179, "")
 , {179} tableEntry(!T, 1#".", Fail, !T.180, "")
 , {180} tableEntry(!T, 1#dq, Fail, MatchAny.181, "")
 , {181} tableEntry(MatchAny, 1#"?", Reduce.73, Fail, "")
 , {182} tableEntry(T, 1#",", Reduce.74, Reduce.75, "")
 , {183} tableEntry(T, 1#"else", T.184, Success*, "")
 , {184} tableEntry(T, 1#"if", NT.185, Success*, "")
 , {185} tableEntry(NT.54, 1#"E", T.186, Success*, "")
 , {186} tableEntry(T, 1#"then", NT.187, Success*, "")
 , {187} tableEntry(NT.54, 1#"E", Reduce*(76, T.183), Success*, "")
 , {188} tableEntry(NT.!T.175, 1#"Id", T.189, Fail, "")
 , {189} tableEntry(T, 1#".", NT.190, NT.191, "")
 , {190} tableEntry(NT.188, 1#"Type", Reduce.77, NT.191, "")
 , {191} tableEntry(NT.!T.175, 1#"Id", Reduce.78, Fail, "")
 , {192} tableEntry(T', 1#"let", MatchAny.193, T'.197, "")
 , {193} tableEntry(MatchAny, 1#"?", T.194, T'.197, "")
 , {194} tableEntry(T, 1#"=", NT.195, T'.197, "")
 , {195} tableEntry(NT.54, 1#"E", NT.196, T'.197, "")
 , {196} tableEntry(NT.T.182, 1#"comma?", Reduce.79, T'.197, "")
 , {197} tableEntry(T', 1#"assert", NT.198, T'.202, "")
 , {198} tableEntry(NT.54, 1#"E", T.199, T'.202, "")
 , {199} tableEntry(T, 1#"report", NT.200, T'.202, "")
 , {200} tableEntry(NT.54, 1#"E", NT.201, T'.202, "")
 , {201} tableEntry(NT.T.182, 1#"comma?", Reduce.80, T'.202, "")
 , {202} tableEntry(T', 1#"{", NT.203, T'.206, "")
 , {203} tableEntry(NT.T.247, 1#"N", T.204, T'.206, "")
 , {204} tableEntry(T, 1#"}", NT.205, T'.206, "")
 , {205} tableEntry(NT.T.182, 1#"comma?", Reduce.81, T'.206, "")
 , {206} tableEntry(T', 1#"for", NT.207, Fail, "")
 , {207} tableEntry(NT.218, 1#"ForDeclare", T'.208, Fail, "")
 , {208} tableEntry(T', 1#"do", NT.209, T.213, "")
 , {209} tableEntry(NT.54, 1#"E", NT.210, T.211, "")
 , {210} tableEntry(NT.T.182, 1#"comma?", Reduce.82, T.211, "")
 , {211} tableEntry(T, 1#"for", NT.212, Fail, "")
 , {212} tableEntry(NT.218, 1#"ForDeclare", T.213, Fail, "")
 , {213} tableEntry(T, 1#"while", NT.214, Fail, "")
 , {214} tableEntry(NT.54, 1#"E", T.215, Fail, "")
 , {215} tableEntry(T, 1#"do", NT.216, Fail, "")
 , {216} tableEntry(NT.54, 1#"E", NT.217, Fail, "")
 , {217} tableEntry(NT.T.182, 1#"comma?", Reduce.83, Fail, "")
 , {218} tableEntry(NT.!T.229, 1#"AccumList", T'.219, Fail, "")
 , {219} tableEntry(T', 1#",", MatchAny.220, T.224, "")
 , {220} tableEntry(MatchAny, 1#"?", T'.221, NT.223, "")
 , {221} tableEntry(T', 1#"∈", NT.222, T.226, "")
 , {222} tableEntry(NT.54, 1#"E", Reduce.84, NT.223, "")
 , {223} tableEntry(NT.!T.229, 1#"AccumList", T.224, Fail, "")
 , {224} tableEntry(T, 1#",", MatchAny.225, NT.228, "")
 , {225} tableEntry(MatchAny, 1#"?", T.226, NT.228, "")
 , {226} tableEntry(T, 1#"/in", NT.227, NT.228, "")
 , {227} tableEntry(NT.54, 1#"E", Reduce.85, NT.228, "")
 , {228} tableEntry(NT.!T.229, 1#"AccumList", Reduce.86, Fail, "")
 , {229} tableEntry(!T, 1#"while", Fail, MatchAny.230, "")
 , {230} tableEntry(MatchAny, 1#"?", T.231, Fail, "")
 , {231} tableEntry(T, 1#"=", NT.232, Fail, "")
 , {232} tableEntry(NT.54, 1#"E", NT.233, Fail, "")
 , {233} tableEntry(NT.T.234, 1#"AccumList'", Reduce.87, Fail, "")
 , {234} tableEntry(T, 1#",", MatchAny.235, Success*, "")
 , {235} tableEntry(MatchAny, 1#"?", T.236, Success*, "")
 , {236} tableEntry(T, 1#"=", NT.237, Success*, "")
 , {237} tableEntry(NT.54, 1#"E", Reduce*(88, T.234), Success*, "")
 , {238} tableEntry(NT.T'.192, 1#"Declare", Reduce*(89, NT.238), Success*, "")
 , {239} tableEntry(NT.MatchAny.243, 1#"FP", NT.240, Fail, "")
 , {240} tableEntry(NT.T.241, 1#"FPL'", Reduce.90, Fail, "")
 , {241} tableEntry(T, 1#",", NT.242, Success*, "")
 , {242} tableEntry(NT.MatchAny.243, 1#"FP", Reduce*(91, T.241), Success*, "")
 , {243} tableEntry(MatchAny, 1#"?", T.244, NT.246, "")
 , {244} tableEntry(T, 1#":", NT.245, NT.246, "")
 , {245} tableEntry(NT.188, 1#"Type", Reduce.92, NT.246, "")
 , {246} tableEntry(NT.188, 1#"Type", Reduce.93, Fail, "")
 , {247} tableEntry(T, 1#"{", NT.248, !T.250, "")
 , {248} tableEntry(NT.T.247, 1#"N", T.249, !T.250, "")
 , {249} tableEntry(T, 1#"}", Discard*.T.247, !T.250, "")
 , {250} tableEntry(!T, 1#"}", All, MatchAny.251, "")
 , {251} tableEntry(MatchAny, 1#"?", Discard*.T.247, All, "")
 , {252} tableEntry(!T, 1#dq, All, !T.253, "")
 , {253} tableEntry(!T, 1#"^", All, MatchAny.254, "")
 , {254} tableEntry(MatchAny, 1#"?", Discard*.!T.252, All, "")
]

function =(seq.word, attribute) boolean true

function $(int) attribute 1#empty:seq.attribute

use standard

use seq.tableEntry

use otherseq.frame

use stack.frame

use otherseq.attribute

use PEGrules

function place(r:runresult) int i.top.stk.r

type frame is
Sstate:state
, Fstate:state
, i:int
, result:seq.attribute
, faili:int
, failresult:seq.attribute

type runresult is stk:stack.frame

Function status(a:runresult) word
if Sstate.top.stk.a ≠ Match then
1#"Failed"
else if place.a = {length of input} faili.top.stk.a then
1#"Match"
else 1#"MatchPrefix"

Function result(a:runresult) attribute 1^result.top.stk.a

function parse(myinput0:seq.word, initAttr:attribute, common:boolean) runresult
let myinput = packed(myinput0 + endMark)
let packedTable = packed.mytable
for
 stk = empty:stack.frame
 , state = startstate
 , i = 1
 , inputi = 1#myinput
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
     next(pop.stk, nextState.Fstate.top, newi, idxNB(myinput, newi), result.top, faili.top, failresult.top)
    else next(
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
  let top = top.stk, next(stk, nextState.state, i, inputi, result.top, i, result.top)
  else if actionState = All then
   let top = top.stk
   let att = [toAttribute(1^result, subseq(myinput, i.top, i - 1))],
   next(pop.stk, Sstate.top, i, inputi, result.top + att, faili.top, failresult.top)
  else if actionState = Lambda then
   let att = [action(reduceNo.state, result, common)],
   next(stk, nextState2.state, i, inputi, result + att, faili, failresult)
  else if actionState = Reduce then
   let top = top.stk
   let att = [action(reduceNo.state, result, common)],
   next(pop.stk, Sstate.top, i, inputi, result.top + att, faili.top, failresult.top)
  else if actionState = Reduce* then
   let att = [action(reduceNo.state, result, common)]
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
    if inputi ≠ match.te then
    {fail} next(stk, Fstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)
    else next(stk, Sstate.te, i + 1, idxNB(myinput, i + 1), result, faili, failresult)
  else if actionState = !T then
   let te = idxNB(packedTable, index.state),
    if inputi = match.te then
    {fail} next(stk, Sstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)
    else next(stk, Fstate.te, i, inputi, result, faili, failresult)
  else if actionState = MatchAny then
   let te = idxNB(packedTable, index.state),
    if inputi = endMark then
    {fail} next(stk, Fstate.te, i, inputi, result, faili, failresult)
    else
     let reslt = result + toAttribute(1^result, [inputi])
     let ini = idxNB(myinput, i + 1),
     next(stk, Sstate.te, i + 1, ini, reslt, faili, failresult)
  else if actionState = T' then
   let te = idxNB(packedTable, index.state),
    if inputi = match.te then
    next(stk, Sstate.te, i + 1, idxNB(myinput, i + 1), result, faili, failresult)
    else next(stk, Fstate.te, i, inputi, result, faili, failresult)
  else
   {match non Terminal}
   let te = idxNB(packedTable, index.state)
   assert action.action.te ∈ [NT, NT*] report "PROBLEM PEG^(state)"
   let newstk = push(stk, frame(Sstate.te, Fstate.te, i, result, faili, failresult))
   let tmp = [toAttribute(1^result, empty:seq.word)],
   next(newstk, nextState.action.te, i, inputi, tmp, i, tmp),
runresult.push(stk, frame(state, state, i, result, n.myinput, result)) 