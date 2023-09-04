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
let r = parse(p, mytable, toAttribute."", true)
let out = text.1_parts.result.r,
if status.r ∈ "Match" then out else "Fail^(p)"

Function prettyNoChange(p:seq.word) seq.word
let r = parse(p, mytable, toAttribute."", false)
let out = text.1_parts.result.r,
if status.r ∈ "Match" then out else "Fail^(p)"

function binary2(a:attribute, b:attribute, op:seq.word) attribute
if isempty.text.1_parts.b then a else attribute(parts.a + parts.b)

function binary(a:attribute, b:attribute, op:seq.word) attribute
let tmp = if isempty.text.1_parts.a then empty:seq.prettyR else parts.a,
attribute(tmp + prettyR(-1, width.op, op) + parts.b)

function checkfirstdigit(chars:seq.char) boolean
let i = if n.chars > 1 ∧ 1_chars = char1."-" then 2 else 1,
between(toint.i_chars, 48, 57)

function unaryMinus(change:boolean, bin:attribute) attribute
let b = if change ∧ prec.1_parts.bin ≤ 2 then removeparen.bin else bin,
attribute.prettyR(2, 1 + width1.b, "-^(text1.b)")

function unaryExp(change:boolean, kind:int, a:attribute, b:attribute) attribute
if kind = 2 then
 if checkfirstdigit.decodeword.1_text1.a then
 attribute.prettyR(0, width1.a + width1.b, text1.a + "." + text1.b)
 else if change then
 funccall(change, a, b, toAttribute."")
 else attribute.prettyR(2, width1.a + width1.b, text1.a + "." + text1.b)
else
 let ce = CommentExp.a,
 attribute.
  if subseq(text1.b, 1, 2) = "<* block" then
   let c = mergelist(2, ce),
   prettyR(prec.1_parts.b, 10000, "<* block^(text1.c) /br^(text1.b << 2)")
  else 1_parts.mergelist(prec.1_parts.b, ce + parts.b)

function mergebinary(change:boolean, prec:int, a0:attribute, b:attribute) attribute
let a1 = 1_parts.a0
let a2 =
 if change ∧ prec.a1 ≤ prec ∧ 1^text.a1 ∈ ") *>" then
  let txt = if prec = 11 then removeclose.text.a1 else removeparen.text.a1,
  [prettyR(prec.a1, width.txt, txt)]
 else parts.a0,
if n.parts.b = 1 ∧ isempty.text.1_parts.b then
attribute.a2
else
 let aa =
  if prec = 1 ∧ prec.1_a2 = 1 then
  [prettyR(0, width.1_a2 + 2, "(^(text.1_a2))")]
  else a2
 for op = true, binary = "", acc = aa, e ∈ parts.b
 do
  if op then
   let t = text.e,
   next(false, if t ∈ [",", ".", "_", "^"] then t else "/sp^(t) /sp", acc)
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
let parts = a + b + parts.E, mergelist(if prec.1_parts = 10 then 10 else 11, parts)
else
 let tmp = removeparen.text1.E
 let e = if tmp = text1.E then 1_parts.E else prettyR(0, width.tmp, tmp),
  if not(n.b = 1 ∧ isempty.text.1_b) then
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
 let tmp = text.1_in
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
     for text = text.1_in, blockIsLast = blockIsLast.text.1_in, e ∈ in << 1
     do
      if isempty.text.e then
      next(text, blockIsLast)
      else if blockIsLast ∨ subseq(text.e, 1, 2) = "<* block" then
      next(text + text.e, blockIsLast.text.e)
      else next(text + "/br" + text.e, blockIsLast.text.e),
     attribute.prettyR(prec, 10000, addblock.text)

function IfExp(change:boolean, prefix:seq.word, R:reduction) seq.prettyR
assert n.parts.2_R = 1 report "PROBLEM"
let adjust = width.prefix + 5
let cond = if change then removeclose.1_R else 1_R
let thenpart = parts.if change then removeclose.2_R else 2_R
let Then = if 1_text.1_thenpart ∈ "-" then "/keyword then /sp" else "/keyword then",
[prettyR(0, width1.cond + adjust, prefix + text1.cond + Then)] + thenpart

function fullIfExp(change:boolean, R:reduction) attribute
let keywordelse = if 1_text1.4_R ∈ "-" then "/keyword else /sp" else "/keyword else"
let prefix = if change then "(/keyword if" else "/keyword if"
let tmp =
 if change then
 let mid = removeclose.4_R, prettyR(9, 6 + width1.mid, keywordelse + text1.mid + ")")
 else prettyR(9, 5 + width1.4_R, keywordelse + text1.4_R),
mergelist(9, IfExp(change, prefix, R) + parts.3_R + tmp)

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
[prettyR(0, width1.a + width1.b + 16, "^(assertpart)^(reportpart)")]
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
  mergebinary(change, 11, attribute.1_parts.accumList, bb)
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
attribute.prettyR(prec.1_parts.a, width1.a + 2, "(^(text1.a))")

function CommentExp(a:attribute) seq.prettyR
let p = 1_parts.a
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

function quote(a:attribute, b:attribute) attribute
let all = parts.a + parts.b
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
let name = text.1_parts.a
let name1 = if 1_name ∈ "+=_-^" then s + "/sp" + name else s + name
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
let newc = if txt = text1.c then 1_parts.c else prettyR(0, width.txt, txt),
toAttribute.removeblock.text1.combine(change, fixname(s, a), parts.b, attribute.newc)

function addBlock(s:seq.prettyR, kind:seq.word) seq.prettyR
let fixes =
 if kind = "literal" then
 ["<* literal /ldq^(escapeformat)", "^(escapeformat)^(dq) *>"]
 else ["<* comment^(escapeformat) {", "}^(escapeformat) *>"],
if n.s = 1 then
[prettyR(0, width.1_s, 1_fixes + text.1_s + 2_fixes)]
else [prettyR(0, 0, 1_fixes)] + s + prettyR(0, 0, 2_fixes)

function slash word 1_"/"

function /All word 1_"All"

function %(b:boolean) seq.word if b then "true" else "false"

function promoteFirstLineOfBLock(s:seq.word) seq.word
{does it work for" a"+" b
 /br c"}
for kk = 0, inescape = false, nesting = 0, continue = true, hasbreak = false, last = 1_"?", w ∈ s
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
if (kk - 1)_s ∈ "/br" then
subseq(s, 1, kk - 2) + "<* block" + s << (kk - 1)
else "<* block^(s)"

function funccall(change:boolean, name:attribute, b:attribute, c:attribute) attribute
let a = 1_parts.b
let aa =
 if change ∧ 1^text.a ∈ ") *>" then
 let txt = removeclose.text.a, prettyR(prec.a, width.a + n.txt - n.text.a, txt)
 else a,
attribute.
 if n.parts.c = 1 ∧ isempty.text1.c then
  if n.parts.name = 0 then
  prettyR(0, width.aa + 4, "[/nosp^(text.aa)]")
  else if change ∧ n.text1.name = 1 ∧ prec.aa ≤ 2 then
  let new = "^(text1.name).^(text.aa)", prettyR(2, width.new, new)
  else if change ∧ prec.aa = 9 then
  prettyR(9, width1.name + 1 + width.aa, "(^(text1.name).^(text.aa))")
  else prettyR(0, width1.name + 2 + width.aa, "^(text1.name) /nosp (^(text.aa))")
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
    next(true, acc + "," + textbb, newblockacc, blockIsLast.textbb, width + width."," + width.bb),
   if n.parts.name = 0 then
    let totalwidth = width + 4,
     if width < maxwidth then
     prettyR(0, totalwidth, "[/nosp^(acc)]")
     else prettyR(0, 10000, "[/nosp^(addblock.blockacc)]")
   else
    let totalwidth = width + width1.name + 2,
     if width < maxwidth then
     prettyR(0, totalwidth, "^(text1.name) /nosp (^(acc))")
     else prettyR(0, totalwidth, "^(text1.name) /nosp (^(addblock.blockacc))")

function endMark word encodeword.[char.254]

function PEGgen(
 seqElementType:word
 , attributeType:attribute
 , runresultType:runresult
 , R:reduction
 , common:boolean
) seq.boolean
[
 "match2code carrot" = 1_"^"
 , "/ slash" = slash
 , "/ dq" = 1_dq
 , "/ any" = 1_"/1"
 , "S function Header Declare' E" = start(common, "function", 1_R, 2_R, 3_R)
 , "/ Function Header Declare' E" = start(common, "Function", 1_R, 2_R, 3_R)
 , "/ type Id is FPL Comment" = start("type", 1_R, attribute(parts.2_R + parts.3_R))
 , "/ Export type:Type Comment" = start("Export type:", 1_R, 2_R)
 , "/ Export Header Comment" = start("Export", 1_R, 2_R)
 , "/ Builtin Header Comment" = start("Builtin", 1_R, 2_R)
 , "/ builtin Header Comment" = start("builtin", 1_R, 2_R)
 , "/ unbound Header Comment" = start("unbound", 1_R, 2_R)
 , "Header Name (FPL) Type"
  = attribute(prettyR(text1.1_R + "/nosp (") + parts.2_R + prettyR.")^(text1.3_R)")
 , "/ Name Type" = attribute(parts.1_R + parts.2_R)
 , "* Comment {N}" = attribute(parts.0_R + CommentExp.1_R)
 , "String dq String' str2 dq" = quote(1_R, 2_R)
 , "* String' str2 carrot (E)"
  = attribute(
   parts.0_R
   + parts.1_R
   + prettyR(
    0
    , width1.2_R + 4
    , "^" + "(^(escapeformat)^(removeparen.text1.2_R)^(escapeformat))"
   )
  )
 , "/ str2 carrot"
  = attribute(parts.0_R + prettyR(0, width1.1_R + 2, text1.1_R + "^"))
 , "/ str2" = attribute(parts.0_R + parts.1_R)
 , "* str2 ! dq ! carrot any" = /All
 , "E Or" = 1_R
 , "* EL', E" = binary(0_R, 1_R, ",")
 , "Or And Or'" = mergebinary(common, 8, 1_R, 2_R)
 , "* Or' ∨ And" = binary(0_R, 1_R, "∨")
 , "/ /or And" = binary(0_R, 1_R, "∨")
 , "/ ⊻ And" = binary(0_R, 1_R, "⊻")
 , "And Compare And'" = mergebinary(common, 7, 1_R, 2_R)
 , "* And' ∧ Compare" = binary(0_R, 1_R, "∧")
 , "/ /and Compare" = binary(0_R, 1_R, "∧")
 , "Compare Sum Compare'" = mergebinary(common, 6, 1_R, 2_R)
 , "* Compare' = Sum" = binary(0_R, 1_R, "=")
 , "/ ≠ Sum" = binary(0_R, 1_R, "≠")
 , "/ > Sum" = binary(0_R, 1_R, ">")
 , "/ < Sum" = binary(0_R, 1_R, "<")
 , "/ >1 Sum" = binary(0_R, 1_R, ">1")
 , "/ >2 Sum" = binary(0_R, 1_R, ">2")
 , "/ ≥ Sum" = binary(0_R, 1_R, "≥")
 , "/ /ge Sum" = binary(0_R, 1_R, "≥")
 , "/ ≤ Sum" = binary(0_R, 1_R, "≤")
 , "/ /le Sum" = binary(0_R, 1_R, "≤")
 , "/ /ne Sum" = binary(0_R, 1_R, "≠")
 , "Sum Product Sum'" = mergebinary(common, 4, 1_R, 2_R)
 , "* Sum'-Product" = binary(0_R, 1_R, "-")
 , "/+Product" = binary(0_R, 1_R, "+")
 , "/ ∈ Product" = binary(0_R, 1_R, "∈")
 , "/ /in Product" = binary(0_R, 1_R, "∈")
 , "/ ∉ Product" = binary(0_R, 1_R, "∉")
 , "/ /nin Product" = binary(0_R, 1_R, "∉")
 , "Product Unary Product'" = mergebinary(common, 3, 1_R, 2_R)
 , "* Product' * Unary" = binary(0_R, 1_R, "*")
 , "/ >> Unary" = binary(0_R, 1_R, ">>")
 , "/ << Unary" = binary(0_R, 1_R, "<<")
 , "/ slash Unary" = binary(0_R, 1_R, [slash])
 , "/ mod Unary" = binary(0_R, 1_R, "mod")
 , "/ ∩ Unary" = binary(0_R, 1_R, "∩")
 , "/ ∪ Unary" = binary(0_R, 1_R, "∪")
 , "/ /cap Unary" = binary(0_R, 1_R, "∩")
 , "/ /cup Unary" = binary(0_R, 1_R, "∪")
 , "/ \ Unary" = binary(0_R, 1_R, "\")
 , "Unary-Unary" = unaryMinus(common, 1_R)
 , "/ Id.Unary" = unaryExp(common, 2, 1_R, 2_R)
 , "/ {N} Unary" = unaryExp(common, 3, 1_R, 2_R)
 , "/ Power" = 1_R
 , "Power Atom Power'" = mergebinary(common, 1, 1_R, 2_R)
 , "* Power'_Unary" = binary(0_R, 1_R, "_")
 , "/^Unary" = binary(0_R, 1_R, "^")
 , "Atom (E)"
  = 
   let a = if common then removeparen.1_R else 1_R,
   attribute.prettyR(prec.1_parts.a, width1.a + 2, "(^(text1.a))")
 , "/ [E EL']" = funccall(common, attribute.empty:seq.prettyR, 1_R, 2_R)
 , "/ String" = 1_R
 , "/ Declare Declare' E"
  = combine(common, empty:seq.prettyR, parts.1_R + parts.2_R, 3_R)
 , "/ if E then E IF else E" = fullIfExp(common, R)
 , "/ Name (E EL')" = funccall(common, 1_R, 2_R, 3_R)
 , "/ Name" = 1_R
 , "Name Id:Type"
  = attribute.prettyR(0, width1.1_R + 2 + width1.2_R, text1.1_R + ":" + text1.2_R)
 , "/ Id" = 1_R
 , "Id !, !] !) !:!.! dq any" = 1_R
 , "comma?," = (toAttribute.if common then "" else ",")
 , "/" = toAttribute.""
 , "* IF else if E then E"
  = attribute(parts.0_R + IfExp(common, "/keyword else /keyword if", R))
 , "Type Id.Type"
  = attribute.prettyR(0, width1.1_R + width1.2_R, text1.1_R + "." + text1.2_R)
 , "/ Id" = 1_R
 , "Declare let any = E comma?" = attribute.LetExp(common, 1_R, 2_R, 3_R)
 , "/ assert E report E comma?" = attribute.AssertExp(common, 1_R, 2_R)
 , "/ {N} comma?" = attribute.CommentExp.1_R
 , "/ for ForDeclare do E comma?" = forExp(1_R, toAttribute."", 2_R, common)
 , "/ for ForDeclare while E do E comma?" = forExp(1_R, 2_R, 3_R, common)
 , "ForDeclare AccumList, any ∈ E" = binary(1_R, AccumExp(common, 2_R, 3_R, "∈"), ",")
 , "/ AccumList, any /in E" = binary(1_R, AccumExp(common, 2_R, 3_R, "∈"), ",")
 , "/ AccumList" = 1_R
 , "AccumList Accum AccumList'"
  = if isempty.text.1_parts.2_R then 1_R else attribute(parts.1_R + parts.2_R)
 , "* AccumList', Accum" = binary(0_R, 1_R, ",")
 , "Accum ! while any = E" = AccumExp(common, 1_R, 2_R, "=")
 , "* Declare' Declare" = attribute(parts.0_R + parts.1_R)
 , "FPL FP FPL'" = attribute(parts.1_R + parts.2_R)
 , "* FPL', FP" = attribute(parts.0_R + prettyR.",^(text1.1_R)")
 , "FP any:Type"
  = attribute.prettyR(0, width1.1_R + 1 + width1.2_R + 1, text1.1_R + ":" + text1.2_R)
 , "/ Type" = 1_R
 , "* N {N}"
  = attribute.prettyR(0, width1.0_R + width1.1_R + 2, text1.0_R + "{^(text1.1_R)}")
 , "/ str1" = attribute.prettyR(0, width1.0_R + width1.1_R, text1.0_R + text1.1_R)
 , "* str1 ! {!} any" = /All
]

<<<< Below is auto generated code >>>>

/br Non-terminals:Accum AccumList AccumList' And And' Atom Comment Compare Compare' Declare Declare'
E EL' FP FPL FPL' ForDeclare Header IF Id N Name Or Or' Power Power' Product Product' S String String'
Sum Sum' Type Unary comma? str1 str2
/br Terminals:() *+,-./and /cap /cup /ge /in /le /ne /nin /or:< << = > >1 >2 >> Builtin Export Function
[\]^_any assert builtin carrot do dq else for function if is let mod report slash then type unbound
while {} ∈ ∉ ∧ ∨ ∩ ∪ ≠ ≤ ≥ ⊻
/br S ← function Header Declare' E / Function Header Declare' E
/br / type Id is FPL Comment
/br / Export type:Type Comment
/br / Export Header Comment
/br / Builtin Header Comment
/br / builtin Header Comment
/br / unbound Header Comment
/br Header ← Name (FPL) Type / Name Type
/br * Comment ← {N}
/br String ← dq String' str2 dq
/br * String' ← str2 carrot (E) / str2 carrot / str2
/br * str2 ← ! dq ! carrot any
/br E ← Or
/br * EL' ←, E
/br Or ← And Or'
/br * Or' ← ∨ And / /or And / ⊻ And
/br And ← Compare And'
/br * And' ← ∧ Compare / /and Compare
/br Compare ← Sum Compare'
/br * Compare' ← = Sum / ≠ Sum / > Sum / < Sum
/br / >1 Sum
/br / >2 Sum
/br / ≥ Sum
/br / /ge Sum
/br / ≤ Sum
/br / /le Sum
/br / /ne Sum
/br Sum ← Product Sum'
/br * Sum' ←-Product /+Product / ∈ Product / /in Product
/br / ∉ Product
/br / /nin Product
/br Product ← Unary Product'
/br * Product' ← * Unary / >> Unary / << Unary / slash Unary
/br / mod Unary
/br / ∩ Unary
/br / ∪ Unary
/br / /cap Unary
/br / /cup Unary
/br / \ Unary
/br Unary ←-Unary / Id.Unary / {N} Unary
/br / Power
/br Power ← Atom Power'
/br * Power' ←_Unary /^Unary
/br Atom ← (E) / [E EL'] / String
/br / Declare Declare' E
/br / if E then E IF else E
/br / Name (E EL')
/br / Name
/br Name ← Id:Type / Id
/br Id ← !, !] !) !:!.! dq any
/br comma? ←, /
/br * IF ← else if E then E
/br Type ← Id.Type / Id
/br Declare ← let any = E comma? / assert E report E comma?
/br / {N} comma?
/br / for ForDeclare do E comma?
/br / for ForDeclare while E do E comma?
/br ForDeclare ← AccumList, any ∈ E / AccumList, any /in E
/br / AccumList
/br AccumList ← Accum AccumList'
/br * AccumList' ←, Accum
/br Accum ← ! while any = E
/br * Declare' ← Declare
/br FPL ← FP FPL'
/br * FPL' ←, FP
/br FP ← any:Type / Type
/br * N ← {N} / str1
/br * str1 ← ! {!} any

function action(
 partno:int
 , R:reduction
 , place:int
 , input:seq.word
 , common:boolean
 , parsestk:stack.frame
) attribute
if partno = 2 then
start(common, "function", 1_R, 2_R, 3_R)
else if partno = 3 then
start(common, "Function", 1_R, 2_R, 3_R)
else if partno = 4 then
start("type", 1_R, attribute(parts.2_R + parts.3_R))
else if partno = 5 then
start("Export type:", 1_R, 2_R)
else if partno = 6 then
start("Export", 1_R, 2_R)
else if partno = 7 then
start("Builtin", 1_R, 2_R)
else if partno = 8 then
start("builtin", 1_R, 2_R)
else if partno = 9 then
start("unbound", 1_R, 2_R)
else if partno = 10 then
attribute(prettyR(text1.1_R + "/nosp (") + parts.2_R + prettyR.")^(text1.3_R)")
else if partno = 11 then
attribute(parts.1_R + parts.2_R)
else if partno = 12 then
attribute(parts.0_R + CommentExp.1_R)
else if partno = 13 then
quote(1_R, 2_R)
else if partno = 14 then
attribute(
 parts.0_R
 + parts.1_R
 + prettyR(
  0
  , width1.2_R + 4
  , "^" + "(^(escapeformat)^(removeparen.text1.2_R)^(escapeformat))"
 )
)
else if partno = 15 then
attribute(parts.0_R + prettyR(0, width1.1_R + 2, text1.1_R + "^"))
else if partno = 16 then
attribute(parts.0_R + parts.1_R)
else if partno = 18 then
1_R
else if partno = 19 then
binary(0_R, 1_R, ",")
else if partno = 20 then
mergebinary(common, 8, 1_R, 2_R)
else if partno = 21 then
binary(0_R, 1_R, "∨")
else if partno = 22 then
binary(0_R, 1_R, "∨")
else if partno = 23 then
binary(0_R, 1_R, "⊻")
else if partno = 24 then
mergebinary(common, 7, 1_R, 2_R)
else if partno = 25 then
binary(0_R, 1_R, "∧")
else if partno = 26 then
binary(0_R, 1_R, "∧")
else if partno = 27 then
mergebinary(common, 6, 1_R, 2_R)
else if partno = 28 then
binary(0_R, 1_R, "=")
else if partno = 29 then
binary(0_R, 1_R, "≠")
else if partno = 30 then
binary(0_R, 1_R, ">")
else if partno = 31 then
binary(0_R, 1_R, "<")
else if partno = 32 then
binary(0_R, 1_R, ">1")
else if partno = 33 then
binary(0_R, 1_R, ">2")
else if partno = 34 then
binary(0_R, 1_R, "≥")
else if partno = 35 then
binary(0_R, 1_R, "≥")
else if partno = 36 then
binary(0_R, 1_R, "≤")
else if partno = 37 then
binary(0_R, 1_R, "≤")
else if partno = 38 then
binary(0_R, 1_R, "≠")
else if partno = 39 then
mergebinary(common, 4, 1_R, 2_R)
else if partno = 40 then
binary(0_R, 1_R, "-")
else if partno = 41 then
binary(0_R, 1_R, "+")
else if partno = 42 then
binary(0_R, 1_R, "∈")
else if partno = 43 then
binary(0_R, 1_R, "∈")
else if partno = 44 then
binary(0_R, 1_R, "∉")
else if partno = 45 then
binary(0_R, 1_R, "∉")
else if partno = 46 then
mergebinary(common, 3, 1_R, 2_R)
else if partno = 47 then
binary(0_R, 1_R, "*")
else if partno = 48 then
binary(0_R, 1_R, ">>")
else if partno = 49 then
binary(0_R, 1_R, "<<")
else if partno = 50 then
binary(0_R, 1_R, [slash])
else if partno = 51 then
binary(0_R, 1_R, "mod")
else if partno = 52 then
binary(0_R, 1_R, "∩")
else if partno = 53 then
binary(0_R, 1_R, "∪")
else if partno = 54 then
binary(0_R, 1_R, "∩")
else if partno = 55 then
binary(0_R, 1_R, "∪")
else if partno = 56 then
binary(0_R, 1_R, "\")
else if partno = 57 then
unaryMinus(common, 1_R)
else if partno = 58 then
unaryExp(common, 2, 1_R, 2_R)
else if partno = 59 then
unaryExp(common, 3, 1_R, 2_R)
else if partno = 60 then
1_R
else if partno = 61 then
mergebinary(common, 1, 1_R, 2_R)
else if partno = 62 then
binary(0_R, 1_R, "_")
else if partno = 63 then
binary(0_R, 1_R, "^")
else if partno = 64 then
 let a = if common then removeparen.1_R else 1_R,
 attribute.prettyR(prec.1_parts.a, width1.a + 2, "(^(text1.a))")
else if partno = 65 then
funccall(common, attribute.empty:seq.prettyR, 1_R, 2_R)
else if partno = 66 then
1_R
else if partno = 67 then
combine(common, empty:seq.prettyR, parts.1_R + parts.2_R, 3_R)
else if partno = 68 then
fullIfExp(common, R)
else if partno = 69 then
funccall(common, 1_R, 2_R, 3_R)
else if partno = 70 then
1_R
else if partno = 71 then
attribute.prettyR(0, width1.1_R + 2 + width1.2_R, text1.1_R + ":" + text1.2_R)
else if partno = 72 then
1_R
else if partno = 73 then
1_R
else if partno = 74 then
toAttribute.if common then "" else ","
else if partno = 75 then
toAttribute.""
else if partno = 76 then
attribute(parts.0_R + IfExp(common, "/keyword else /keyword if", R))
else if partno = 77 then
attribute.prettyR(0, width1.1_R + width1.2_R, text1.1_R + "." + text1.2_R)
else if partno = 78 then
1_R
else if partno = 79 then
attribute.LetExp(common, 1_R, 2_R, 3_R)
else if partno = 80 then
attribute.AssertExp(common, 1_R, 2_R)
else if partno = 81 then
attribute.CommentExp.1_R
else if partno = 82 then
forExp(1_R, toAttribute."", 2_R, common)
else if partno = 83 then
forExp(1_R, 2_R, 3_R, common)
else if partno = 84 then
binary(1_R, AccumExp(common, 2_R, 3_R, "∈"), ",")
else if partno = 85 then
binary(1_R, AccumExp(common, 2_R, 3_R, "∈"), ",")
else if partno = 86 then
1_R
else if partno = 87 then
if isempty.text.1_parts.2_R then 1_R else attribute(parts.1_R + parts.2_R)
else if partno = 88 then
binary(0_R, 1_R, ",")
else if partno = 89 then
AccumExp(common, 1_R, 2_R, "=")
else if partno = 90 then
attribute(parts.0_R + parts.1_R)
else if partno = 91 then
attribute(parts.1_R + parts.2_R)
else if partno = 92 then
attribute(parts.0_R + prettyR.",^(text1.1_R)")
else if partno = 93 then
attribute.prettyR(0, width1.1_R + 1 + width1.2_R + 1, text1.1_R + ":" + text1.2_R)
else if partno = 94 then
1_R
else if partno = 95 then
attribute.prettyR(0, width1.0_R + width1.1_R + 2, text1.0_R + "{^(text1.1_R)}")
else if partno = 96 then
attribute.prettyR(0, width1.0_R + width1.1_R, text1.0_R + text1.1_R)
else 0_R

function mytable seq.tableEntry
[
 {1} tableEntry(MatchNT.Match.2, 1_"?", Reduce.1, Reduce, "")
 , {2} tableEntry(Match, 1_"function", S.3, Match.6, "")
 , {3} tableEntry(MatchNT.S.32, 1_"?", S.4, S.21, "")
 , {4} tableEntry(MatchNT.S.240, 1_"?", S.5, Match.6, "")
 , {5} tableEntry(MatchNT.S.57, 1_"?", Reduce.2, Match.6, "")
 , {6} tableEntry(Match, 1_"Function", S.7, Match.10, "")
 , {7} tableEntry(MatchNT.S.32, 1_"?", S.8, Match.10, "")
 , {8} tableEntry(MatchNT.S.240, 1_"?", S.9, Match.10, "")
 , {9} tableEntry(MatchNT.S.57, 1_"?", Reduce.3, Match.10, "")
 , {10} tableEntry(Match, 1_"type", S.11, Match.15, "")
 , {11} tableEntry(MatchNT.!Match.178, 1_"?", Match.12, Match.15, "")
 , {12} tableEntry(Match, 1_"is", S.13, Match.15, "")
 , {13} tableEntry(MatchNT.S.241, 1_"?", S.14, Match.15, "")
 , {14} tableEntry(MatchNT.Match.39, 1_"?", Reduce.4, Match.15, "")
 , {15} tableEntry(Match, 1_"Export", Match.16, Match.20, "")
 , {16} tableEntry(Match, 1_"type", Match.17, Match.20, "")
 , {17} tableEntry(Match, 1_":", S.18, Match.20, "")
 , {18} tableEntry(MatchNT.S.191, 1_"?", S.19, Match.20, "")
 , {19} tableEntry(MatchNT.Match.39, 1_"?", Reduce.5, Match.20, "")
 , {20} tableEntry(Match, 1_"Export", S.21, Match.23, "")
 , {21} tableEntry(MatchNT.S.32, 1_"?", S.22, Match.23, "")
 , {22} tableEntry(MatchNT.Match.39, 1_"?", Reduce.6, Match.23, "")
 , {23} tableEntry(Match, 1_"Builtin", S.24, Match.26, "")
 , {24} tableEntry(MatchNT.S.32, 1_"?", S.25, Match.26, "")
 , {25} tableEntry(MatchNT.Match.39, 1_"?", Reduce.7, Match.26, "")
 , {26} tableEntry(Match, 1_"builtin", S.27, Match.29, "")
 , {27} tableEntry(MatchNT.S.32, 1_"?", S.28, Match.29, "")
 , {28} tableEntry(MatchNT.Match.39, 1_"?", Reduce.8, Match.29, "")
 , {29} tableEntry(Match, 1_"unbound", S.30, Fail, "")
 , {30} tableEntry(MatchNT.S.32, 1_"?", S.31, Fail, "")
 , {31} tableEntry(MatchNT.Match.39, 1_"?", Reduce.9, Fail, "")
 , {32} tableEntry(MatchNT.S.174, 1_"?", MatchNext.33, S.37, "")
 , {33} tableEntry(MatchNext, 1_"(", S.34, S.38, "")
 , {34} tableEntry(MatchNT.S.241, 1_"?", Match.35, S.37, "")
 , {35} tableEntry(Match, 1_")", S.36, S.37, "")
 , {36} tableEntry(MatchNT.S.191, 1_"?", Reduce.10, S.37, "")
 , {37} tableEntry(MatchNT.S.174, 1_"?", S.38, Fail, "")
 , {38} tableEntry(MatchNT.S.191, 1_"?", Reduce.11, Fail, "")
 , {39} tableEntry(Match, 1_"{", S.40, Success*, "")
 , {40} tableEntry(MatchNT.Match.249, 1_"?", Match.41, Success*, "")
 , {41} tableEntry(Match, 1_"}", Reduce(12, Match.39), Success*, "")
 , {42} tableEntry(Match, 1_dq, S.43, Fail, "")
 , {43} tableEntry(MatchNT.S.46, 1_"?", S.44, Fail, "")
 , {44} tableEntry(MatchNT.!Match.54, 1_"?", Match.45, Fail, "")
 , {45} tableEntry(Match, 1_dq, Reduce.13, Fail, "")
 , {46} tableEntry(MatchNT.!Match.54, 1_"?", MatchNext.47, S.51, "")
 , {47} tableEntry(MatchNext, 1_"^", MatchNext.48, Match.52, "")
 , {48} tableEntry(MatchNext, 1_"(", S.49, Reduce(15, S.46), "")
 , {49} tableEntry(MatchNT.S.57, 1_"?", Match.50, S.51, "")
 , {50} tableEntry(Match, 1_")", Reduce(14, S.46), S.51, "")
 , {51} tableEntry(MatchNT.!Match.54, 1_"?", Match.52, S.53, "")
 , {52} tableEntry(Match, 1_"^", Reduce(15, S.46), S.53, "")
 , {53} tableEntry(MatchNT.!Match.54, 1_"?", Reduce(16, S.46), Success*, "")
 , {54} tableEntry(!Match, 1_dq, All, !Match.55, "")
 , {55} tableEntry(!Match, 1_"^", All, MatchAny.56, "")
 , {56} tableEntry(MatchAny, 1_"?", Discard*.!Match.54, All, "")
 , {57} tableEntry(MatchNT.S.60, 1_"?", Reduce.18, Fail, "")
 , {58} tableEntry(Match, 1_",", S.59, Success*, "")
 , {59} tableEntry(MatchNT.S.57, 1_"?", Reduce(19, Match.58), Success*, "")
 , {60} tableEntry(MatchNT.S.68, 1_"?", S.61, Fail, "")
 , {61} tableEntry(MatchNT.Match.62, 1_"?", Reduce.20, Fail, "")
 , {62} tableEntry(Match, 1_"∨", S.63, Match.64, "")
 , {63} tableEntry(MatchNT.S.68, 1_"?", Reduce(21, Match.62), Match.64, "")
 , {64} tableEntry(Match, 1_"/or", S.65, Match.66, "")
 , {65} tableEntry(MatchNT.S.68, 1_"?", Reduce(22, Match.62), Match.66, "")
 , {66} tableEntry(Match, 1_"⊻", S.67, Success*, "")
 , {67} tableEntry(MatchNT.S.68, 1_"?", Reduce(23, Match.62), Success*, "")
 , {68} tableEntry(MatchNT.S.74, 1_"?", S.69, Fail, "")
 , {69} tableEntry(MatchNT.Match.70, 1_"?", Reduce.24, Fail, "")
 , {70} tableEntry(Match, 1_"∧", S.71, Match.72, "")
 , {71} tableEntry(MatchNT.S.74, 1_"?", Reduce(25, Match.70), Match.72, "")
 , {72} tableEntry(Match, 1_"/and", S.73, Success*, "")
 , {73} tableEntry(MatchNT.S.74, 1_"?", Reduce(26, Match.70), Success*, "")
 , {74} tableEntry(MatchNT.S.98, 1_"?", S.75, Fail, "")
 , {75} tableEntry(MatchNT.Match.76, 1_"?", Reduce.27, Fail, "")
 , {76} tableEntry(Match, 1_"=", S.77, Match.78, "")
 , {77} tableEntry(MatchNT.S.98, 1_"?", Reduce(28, Match.76), Match.78, "")
 , {78} tableEntry(Match, 1_"≠", S.79, Match.80, "")
 , {79} tableEntry(MatchNT.S.98, 1_"?", Reduce(29, Match.76), Match.80, "")
 , {80} tableEntry(Match, 1_">", S.81, Match.82, "")
 , {81} tableEntry(MatchNT.S.98, 1_"?", Reduce(30, Match.76), Match.82, "")
 , {82} tableEntry(Match, 1_"<", S.83, Match.84, "")
 , {83} tableEntry(MatchNT.S.98, 1_"?", Reduce(31, Match.76), Match.84, "")
 , {84} tableEntry(Match, 1_">1", S.85, Match.86, "")
 , {85} tableEntry(MatchNT.S.98, 1_"?", Reduce(32, Match.76), Match.86, "")
 , {86} tableEntry(Match, 1_">2", S.87, Match.88, "")
 , {87} tableEntry(MatchNT.S.98, 1_"?", Reduce(33, Match.76), Match.88, "")
 , {88} tableEntry(Match, 1_"≥", S.89, Match.90, "")
 , {89} tableEntry(MatchNT.S.98, 1_"?", Reduce(34, Match.76), Match.90, "")
 , {90} tableEntry(Match, 1_"/ge", S.91, Match.92, "")
 , {91} tableEntry(MatchNT.S.98, 1_"?", Reduce(35, Match.76), Match.92, "")
 , {92} tableEntry(Match, 1_"≤", S.93, Match.94, "")
 , {93} tableEntry(MatchNT.S.98, 1_"?", Reduce(36, Match.76), Match.94, "")
 , {94} tableEntry(Match, 1_"/le", S.95, Match.96, "")
 , {95} tableEntry(MatchNT.S.98, 1_"?", Reduce(37, Match.76), Match.96, "")
 , {96} tableEntry(Match, 1_"/ne", S.97, Success*, "")
 , {97} tableEntry(MatchNT.S.98, 1_"?", Reduce(38, Match.76), Success*, "")
 , {98} tableEntry(MatchNT.S.112, 1_"?", S.99, Fail, "")
 , {99} tableEntry(MatchNT.Match.100, 1_"?", Reduce.39, Fail, "")
 , {100} tableEntry(Match, 1_"-", S.101, Match.102, "")
 , {101} tableEntry(MatchNT.S.112, 1_"?", Reduce(40, Match.100), Match.102, "")
 , {102} tableEntry(Match, 1_"+", S.103, Match.104, "")
 , {103} tableEntry(MatchNT.S.112, 1_"?", Reduce(41, Match.100), Match.104, "")
 , {104} tableEntry(Match, 1_"∈", S.105, Match.106, "")
 , {105} tableEntry(MatchNT.S.112, 1_"?", Reduce(42, Match.100), Match.106, "")
 , {106} tableEntry(Match, 1_"/in", S.107, Match.108, "")
 , {107} tableEntry(MatchNT.S.112, 1_"?", Reduce(43, Match.100), Match.108, "")
 , {108} tableEntry(Match, 1_"∉", S.109, Match.110, "")
 , {109} tableEntry(MatchNT.S.112, 1_"?", Reduce(44, Match.100), Match.110, "")
 , {110} tableEntry(Match, 1_"/nin", S.111, Success*, "")
 , {111} tableEntry(MatchNT.S.112, 1_"?", Reduce(45, Match.100), Success*, "")
 , {112} tableEntry(MatchNT.Match.134, 1_"?", S.113, Fail, "")
 , {113} tableEntry(MatchNT.Match.114, 1_"?", Reduce.46, Fail, "")
 , {114} tableEntry(Match, 1_"*", S.115, Match.116, "")
 , {115} tableEntry(MatchNT.Match.134, 1_"?", Reduce(47, Match.114), Match.116, "")
 , {116} tableEntry(Match, 1_">>", S.117, Match.118, "")
 , {117} tableEntry(MatchNT.Match.134, 1_"?", Reduce(48, Match.114), Match.118, "")
 , {118} tableEntry(Match, 1_"<<", S.119, Match.120, "")
 , {119} tableEntry(MatchNT.Match.134, 1_"?", Reduce(49, Match.114), Match.120, "")
 , {120} tableEntry(Match, slash, S.121, Match.122, "")
 , {121} tableEntry(MatchNT.Match.134, 1_"?", Reduce(50, Match.114), Match.122, "")
 , {122} tableEntry(Match, 1_"mod", S.123, Match.124, "")
 , {123} tableEntry(MatchNT.Match.134, 1_"?", Reduce(51, Match.114), Match.124, "")
 , {124} tableEntry(Match, 1_"∩", S.125, Match.126, "")
 , {125} tableEntry(MatchNT.Match.134, 1_"?", Reduce(52, Match.114), Match.126, "")
 , {126} tableEntry(Match, 1_"∪", S.127, Match.128, "")
 , {127} tableEntry(MatchNT.Match.134, 1_"?", Reduce(53, Match.114), Match.128, "")
 , {128} tableEntry(Match, 1_"/cap", S.129, Match.130, "")
 , {129} tableEntry(MatchNT.Match.134, 1_"?", Reduce(54, Match.114), Match.130, "")
 , {130} tableEntry(Match, 1_"/cup", S.131, Match.132, "")
 , {131} tableEntry(MatchNT.Match.134, 1_"?", Reduce(55, Match.114), Match.132, "")
 , {132} tableEntry(Match, 1_"\", S.133, Success*, "")
 , {133} tableEntry(MatchNT.Match.134, 1_"?", Reduce(56, Match.114), Success*, "")
 , {134} tableEntry(Match, 1_"-", S.135, S.136, "")
 , {135} tableEntry(MatchNT.Match.134, 1_"?", Reduce.57, S.136, "")
 , {136} tableEntry(MatchNT.!Match.178, 1_"?", Match.137, Match.139, "")
 , {137} tableEntry(Match, 1_".", S.138, Match.139, "")
 , {138} tableEntry(MatchNT.Match.134, 1_"?", Reduce.58, Match.139, "")
 , {139} tableEntry(Match, 1_"{", S.140, S.143, "")
 , {140} tableEntry(MatchNT.Match.249, 1_"?", Match.141, S.143, "")
 , {141} tableEntry(Match, 1_"}", S.142, S.143, "")
 , {142} tableEntry(MatchNT.Match.134, 1_"?", Reduce.59, S.143, "")
 , {143} tableEntry(MatchNT.S.144, 1_"?", Reduce.60, Fail, "")
 , {144} tableEntry(MatchNT.Match.150, 1_"?", S.145, Fail, "")
 , {145} tableEntry(MatchNT.Match.146, 1_"?", Reduce.61, Fail, "")
 , {146} tableEntry(Match, 1_"_", S.147, Match.148, "")
 , {147} tableEntry(MatchNT.Match.134, 1_"?", Reduce(62, Match.146), Match.148, "")
 , {148} tableEntry(Match, 1_"^", S.149, Success*, "")
 , {149} tableEntry(MatchNT.Match.134, 1_"?", Reduce(63, Match.146), Success*, "")
 , {150} tableEntry(Match, 1_"(", S.151, Match.153, "")
 , {151} tableEntry(MatchNT.S.57, 1_"?", Match.152, Reduce.70, "")
 , {152} tableEntry(Match, 1_")", Reduce.64, Match.153, "")
 , {153} tableEntry(Match, 1_"[", S.154, S.157, "")
 , {154} tableEntry(MatchNT.S.57, 1_"?", S.155, S.157, "")
 , {155} tableEntry(MatchNT.Match.58, 1_"?", Match.156, S.157, "")
 , {156} tableEntry(Match, 1_"]", Reduce.65, S.157, "")
 , {157} tableEntry(MatchNT.Match.42, 1_"?", Reduce.66, S.158, "")
 , {158} tableEntry(MatchNT.Match.195, 1_"?", S.159, Match.161, "")
 , {159} tableEntry(MatchNT.S.240, 1_"?", S.160, Match.161, "")
 , {160} tableEntry(MatchNT.S.57, 1_"?", Reduce.67, Match.161, "")
 , {161} tableEntry(Match, 1_"if", S.162, S.168, "")
 , {162} tableEntry(MatchNT.S.57, 1_"?", Match.163, S.168, "")
 , {163} tableEntry(Match, 1_"then", S.164, S.168, "")
 , {164} tableEntry(MatchNT.S.57, 1_"?", S.165, S.168, "")
 , {165} tableEntry(MatchNT.Match.186, 1_"?", Match.166, S.168, "")
 , {166} tableEntry(Match, 1_"else", S.167, S.168, "")
 , {167} tableEntry(MatchNT.S.57, 1_"?", Reduce.68, S.168, "")
 , {168} tableEntry(MatchNT.S.174, 1_"?", Match.169, S.173, "")
 , {169} tableEntry(Match, 1_"(", S.170, S.173, "")
 , {170} tableEntry(MatchNT.S.57, 1_"?", S.171, S.173, "")
 , {171} tableEntry(MatchNT.Match.58, 1_"?", Match.172, S.173, "")
 , {172} tableEntry(Match, 1_")", Reduce.69, S.173, "")
 , {173} tableEntry(MatchNT.S.174, 1_"?", Reduce.70, Fail, "")
 , {174} tableEntry(MatchNT.!Match.178, 1_"?", MatchNext.175, S.177, "")
 , {175} tableEntry(MatchNext, 1_":", S.176, Reduce.72, "")
 , {176} tableEntry(MatchNT.S.191, 1_"?", Reduce.71, S.177, "")
 , {177} tableEntry(MatchNT.!Match.178, 1_"?", Reduce.72, Fail, "")
 , {178} tableEntry(!Match, 1_",", Fail, !Match.179, "")
 , {179} tableEntry(!Match, 1_"]", Fail, !Match.180, "")
 , {180} tableEntry(!Match, 1_")", Fail, !Match.181, "")
 , {181} tableEntry(!Match, 1_":", Fail, !Match.182, "")
 , {182} tableEntry(!Match, 1_".", Fail, !Match.183, "")
 , {183} tableEntry(!Match, 1_dq, Fail, MatchAny.184, "")
 , {184} tableEntry(MatchAny, 1_"?", Reduce.73, Fail, "")
 , {185} tableEntry(Match, 1_",", Reduce.74, Reduce.75, "")
 , {186} tableEntry(Match, 1_"else", Match.187, Success*, "")
 , {187} tableEntry(Match, 1_"if", S.188, Success*, "")
 , {188} tableEntry(MatchNT.S.57, 1_"?", Match.189, Success*, "")
 , {189} tableEntry(Match, 1_"then", S.190, Success*, "")
 , {190} tableEntry(MatchNT.S.57, 1_"?", Reduce(76, Match.186), Success*, "")
 , {191} tableEntry(MatchNT.!Match.178, 1_"?", MatchNext.192, S.194, "")
 , {192} tableEntry(MatchNext, 1_".", S.193, Reduce.78, "")
 , {193} tableEntry(MatchNT.S.191, 1_"?", Reduce.77, S.194, "")
 , {194} tableEntry(MatchNT.!Match.178, 1_"?", Reduce.78, Fail, "")
 , {195} tableEntry(Match, 1_"let", MatchAny.196, Match.200, "")
 , {196} tableEntry(MatchAny, 1_"?", MatchNext.197, S.215, "")
 , {197} tableEntry(MatchNext, 1_"=", S.198, Match.216, "")
 , {198} tableEntry(MatchNT.S.57, 1_"?", S.199, Match.200, "")
 , {199} tableEntry(MatchNT.Match.185, 1_"?", Reduce.79, Match.200, "")
 , {200} tableEntry(Match, 1_"assert", S.201, Match.205, "")
 , {201} tableEntry(MatchNT.S.57, 1_"?", Match.202, Match.205, "")
 , {202} tableEntry(Match, 1_"report", S.203, Match.205, "")
 , {203} tableEntry(MatchNT.S.57, 1_"?", S.204, Match.205, "")
 , {204} tableEntry(MatchNT.Match.185, 1_"?", Reduce.80, Match.205, "")
 , {205} tableEntry(Match, 1_"{", S.206, Match.209, "")
 , {206} tableEntry(MatchNT.Match.249, 1_"?", Match.207, Match.209, "")
 , {207} tableEntry(Match, 1_"}", S.208, Match.209, "")
 , {208} tableEntry(MatchNT.Match.185, 1_"?", Reduce.81, Match.209, "")
 , {209} tableEntry(Match, 1_"for", S.210, Match.214, "")
 , {210} tableEntry(MatchNT.S.221, 1_"?", Match.211, Match.214, "")
 , {211} tableEntry(Match, 1_"do", S.212, Match.214, "")
 , {212} tableEntry(MatchNT.S.57, 1_"?", S.213, Match.214, "")
 , {213} tableEntry(MatchNT.Match.185, 1_"?", Reduce.82, Match.214, "")
 , {214} tableEntry(Match, 1_"for", S.215, Fail, "")
 , {215} tableEntry(MatchNT.S.221, 1_"?", Match.216, Fail, "")
 , {216} tableEntry(Match, 1_"while", S.217, Fail, "")
 , {217} tableEntry(MatchNT.S.57, 1_"?", Match.218, Fail, "")
 , {218} tableEntry(Match, 1_"do", S.219, Fail, "")
 , {219} tableEntry(MatchNT.S.57, 1_"?", S.220, Fail, "")
 , {220} tableEntry(MatchNT.Match.185, 1_"?", Reduce.83, Fail, "")
 , {221} tableEntry(MatchNT.S.232, 1_"?", MatchNext.222, S.226, "")
 , {222} tableEntry(MatchNext, 1_",", MatchAny.223, Match.227, "")
 , {223} tableEntry(MatchAny, 1_"?", MatchNext.224, MatchAny.228, "")
 , {224} tableEntry(MatchNext, 1_"∈", S.225, Match.229, "")
 , {225} tableEntry(MatchNT.S.57, 1_"?", Reduce.84, S.226, "")
 , {226} tableEntry(MatchNT.S.232, 1_"?", Match.227, S.231, "")
 , {227} tableEntry(Match, 1_",", MatchAny.228, S.231, "")
 , {228} tableEntry(MatchAny, 1_"?", Match.229, S.231, "")
 , {229} tableEntry(Match, 1_"/in", S.230, S.231, "")
 , {230} tableEntry(MatchNT.S.57, 1_"?", Reduce.85, S.231, "")
 , {231} tableEntry(MatchNT.S.232, 1_"?", Reduce.86, Fail, "")
 , {232} tableEntry(MatchNT.!Match.236, 1_"?", S.233, Fail, "")
 , {233} tableEntry(MatchNT.Match.234, 1_"?", Reduce.87, Fail, "")
 , {234} tableEntry(Match, 1_",", S.235, Success*, "")
 , {235} tableEntry(MatchNT.!Match.236, 1_"?", Reduce(88, Match.234), Success*, "")
 , {236} tableEntry(!Match, 1_"while", Fail, MatchAny.237, "")
 , {237} tableEntry(MatchAny, 1_"?", Match.238, Fail, "")
 , {238} tableEntry(Match, 1_"=", S.239, Fail, "")
 , {239} tableEntry(MatchNT.S.57, 1_"?", Reduce.89, Fail, "")
 , {240} tableEntry(MatchNT.Match.195, 1_"?", Reduce(90, S.240), Success*, "")
 , {241} tableEntry(MatchNT.MatchAny.245, 1_"?", S.242, Fail, "")
 , {242} tableEntry(MatchNT.Match.243, 1_"?", Reduce.91, Fail, "")
 , {243} tableEntry(Match, 1_",", S.244, Success*, "")
 , {244} tableEntry(MatchNT.MatchAny.245, 1_"?", Reduce(92, Match.243), Success*, "")
 , {245} tableEntry(MatchAny, 1_"?", Match.246, S.248, "")
 , {246} tableEntry(Match, 1_":", S.247, S.248, "")
 , {247} tableEntry(MatchNT.S.191, 1_"?", Reduce.93, S.248, "")
 , {248} tableEntry(MatchNT.S.191, 1_"?", Reduce.94, Fail, "")
 , {249} tableEntry(Match, 1_"{", S.250, S.252, "")
 , {250} tableEntry(MatchNT.Match.249, 1_"?", Match.251, S.252, "")
 , {251} tableEntry(Match, 1_"}", Reduce(95, Match.249), S.252, "")
 , {252} tableEntry(MatchNT.!Match.253, 1_"?", Reduce(96, Match.249), Success*, "")
 , {253} tableEntry(!Match, 1_"{", All, !Match.254, "")
 , {254} tableEntry(!Match, 1_"}", All, MatchAny.255, "")
 , {255} tableEntry(MatchAny, 1_"?", Discard*.!Match.253, All, "")
]

function =(seq.word, attribute) boolean true

function =(seq.word, word) boolean true

use standard

use seq.tableEntry

use otherseq.frame

use stack.frame

use otherseq.attribute

use PEGrules

function _(i:int, R:reduction) attribute (i + 1)_toseq.R

type reduction is toseq:seq.attribute

type frame is
Sstate:state
, Fstate:state
, i:int
, result:seq.attribute
, faili:int
, failresult:seq.attribute

type runresult is stk:stack.frame

Function status(a:runresult) word
if Sstate.top.stk.a ≠ Reduce.1 then
1_"Failed"
else if i.top.stk.a = {length of input} faili.top.stk.a then
1_"Match"
else 1_"MatchPrefix"

Function result(a:runresult) attribute 1^result.top.stk.a

function parse(
 myinput0:seq.word
 , table:seq.tableEntry
 , initAttr:attribute
 , common:boolean
) runresult
let myinput = packed(myinput0 + endMark)
let packedTable = packed.table
for
 stk = empty:stack.frame
 , state = startstate
 , i = 1
 , inputi = 1_myinput
 , result = [initAttr]
 , faili = 1
 , failresult = [initAttr]
while not(state = Reduce.1 ∨ state = Reduce.0)
do
 let actionState = action.state,
  if actionState = Fail then
   {goto Fstate.top.stk, i = faili.top, pop.stk, discard result}
   let top = top.stk
   let newstk = pop.stk,
   next(
    newstk
    , if is!.Sstate.top then Sstate.top else Fstate.top
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
  else if actionState = SuccessDiscard* then
   {goto Sstate.top.stk, pop.stk, keep result}
   let top = top.stk, next(pop.stk, Sstate.top, i, inputi, result.top, faili.top, failresult.top)
  else if actionState = Discard* then
  let top = top.stk, next(stk, nextState.state, i, inputi, result.top, i, result.top)
  else if actionState = All then
   let top = top.stk
   let att = [toAttribute(1^result, subseq(myinput, i.top, i - 1))],
   next(pop.stk, Sstate.top, i, inputi, result.top + att, faili.top, failresult.top)
  else if actionState = Reduce then
   {Reduce}
   if nextState.state ≠ S.0 then
    let att = [action(reduceNo.state, reduction.result, i, myinput, common, stk)]
    let top = top.stk,
     if faili = i then
     next(pop.stk, Sstate.top, i, inputi, result.top + att, faili.top, failresult.top)
     else next(stk, nextState.state, i, inputi, att, i, att)
   else
    let top = top.stk,
     if is!.Sstate.top then
      {goto Fstate.top.stk, i = faili.top, pop.stk, discard result}
      let newstk = pop.stk
      let newi = faili.top
      let ini = idxNB(myinput, newi),
      next(newstk, Fstate.top, newi, ini, failresult.top, faili.top, failresult.top)
     else
      let att = [action(reduceNo.state, reduction.result, i, myinput, common, stk)],
      next(pop.stk, Sstate.top, i, inputi, result.top + att, faili.top, failresult.top)
  else if actionState = Match then
   let te = idxNB(packedTable, index.state),
    if inputi ≠ match.te then
    {fail} next(stk, Fstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)
    else next(stk, Sstate.te, i + 1, idxNB(myinput, i + 1), result, faili, failresult)
  else if actionState = !Match then
   let te = idxNB(packedTable, index.state),
    if inputi = match.te then
    {fail} next(stk, Sstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)
    else next(stk, Fstate.te, i, inputi, result, faili, failresult)
  else if actionState = MatchAny then
   let te = idxNB(packedTable, index.state),
    if inputi = endMark then
    {fail} next(stk, Fstate.te, i, inputi, result, faili, failresult)
    else
     let reslt =
      if action.Sstate.te = Discard* then
      result
      else result + toAttribute(1^result, [inputi])
     let ini = idxNB(myinput, i + 1),
     next(stk, Sstate.te, i + 1, ini, reslt, faili, failresult)
  else if actionState = MatchNext then
   let te = idxNB(packedTable, index.state),
    if inputi = match.te then
    next(stk, Sstate.te, i + 1, idxNB(myinput, i + 1), result, faili, failresult)
    else next(stk, Fstate.te, i, inputi, result, faili, failresult)
  else
   {match non Terminal}
   let te = idxNB(packedTable, index.state)
   assert action.action.te = MatchNT report "PROBLEM PEG^(state)"
   let newstk = push(stk, frame(Sstate.te, Fstate.te, i, result, faili, failresult))
   let tmp = [toAttribute(1^result, empty:seq.word)],
   next(newstk, nextState.action.te, i, inputi, tmp, i, tmp),
runresult.push(stk, frame(state, state, i, result, n.myinput, result)) 