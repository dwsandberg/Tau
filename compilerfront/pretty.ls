Module pretty

use file

use seq.file

use seq.filename

use otherseq.mytype

use prettyR

use standard

use seq.symbol

use set.symbol

use symbol2

use set.symlink

use otherseq.word

use seq.word

use seq.seq.word

use set.seq.word

Export escapeformat(seq.word) seq.word {From prettyR}

Export id(symbol) seq.word {From prettyR}

Export type:symlink {From prettyR}

Export file(symlink) seq.word {From prettyR}

Export id(symlink) seq.word {From prettyR}

Export symlink(seq.word, seq.word) symlink {From prettyR}

Export >1(a:symlink, b:symlink) ordering {From prettyR}

Export pretty(
header:seq.word
, code:seq.symbol
, syms:set.symlink
, change:boolean
) seq.word
{From prettyR}

Export getheader(s:seq.word) seq.word {From prettySupport}

Export showZ(seq.word) seq.word {From prettySupport}

function #(a:int, b:int) int a - b

function testing int 1#(2#3) + (1#2)#3

Function sortuse(b:seq.seq.word, prefix:seq.word) seq.seq.word
for a = empty:seq.seq.word, u ∈ b do a + reverse.u
for acc = empty:seq.seq.word, @e ∈ alphasort.toseq.asset.a
do acc + (prefix + reverse.@e),
acc

function formatHeader(p:seq.word) seq.word
if width.p < maxwidth then p
else
 let i = findindex(p, 1#"("),
 if i > n.p then p
 else
  for acc = subseq(p, 1, i), e ∈ break(p << i, ",)", true)
  do acc + "/br" + e,
  acc

Function pretty(p:seq.word) seq.word pretty(p, true)

Function prettyNoChange(p:seq.word) seq.word pretty(p, false)

Function libsrc(m:midpoint, outfn:seq.filename) seq.file
let outname = 1#outfn
for only = "", fn ∈ outfn
do if ext.fn ∈ "libsrc" then only + name.fn else only
for
 libname = 1#"?"
 , all = ""
 , libtxt = ""
 , libs = empty:seq.file
 , p ∈ src.m << 1 + ["#File:+?"]
do
 if subseq(p, 1, 3) = "#File:" ∧ n.p > 4 then
  let newlibname = 5#p,
  if newlibname = libname then next(newlibname, all, libtxt, libs)
  else
   let newlibs =
    if libname ∉ only ∨ isempty.libtxt then libs
    else libs + file(filename("+^(dirpath.outname)" + libname + ".libsrc"), libtxt),
   next(newlibname, all + "/p" + libtxt, p, newlibs)
 else
  let newtxt =
   if subseq(p, 1, 1) ∈ ["Function", "function", "Export", "type"] then prettyNoChange.p
   else escapeformat.p,
  next(libname, all, libtxt + "/p" + newtxt, libs),
[file(changeext(outname, "libsrc"), all)] + libs

function pretty(p:seq.word, change:boolean) seq.word
if 1#p ∈ "Function function" then
 let r = parse(p, empty:seq.symbol),
 if status.r ∈ "Match MatchPrefix" then pretty(formatHeader.getheader.p, result.r, empty:set.symlink, change)
 else [status.r] + %.result.r
else if 1#p ∈ "Export unbound Builtin builtin" then
 let h = formatHeader.getheader.p
 let rest = p << (findindex(p, 1#"{") - 1),
 if width(h + rest) < maxwidth then h + rest else h + "/br" + rest
else if 1#p ∈ "type" then
 if width.p < maxwidth then p
 else
  for acc = subseq(p, 1, 3), e ∈ break(p << 3, ",", true)
  do acc + "/br" + e,
  acc
else p

function toAttribute(b:seq.symbol, w:seq.word) seq.symbol
if isempty.w then empty:seq.symbol else [Words.w]

function endMark word encodeword.[char.254]

function slash word 1#"/"

function worddata(s:seq.symbol) seq.word
for acc = "", e ∈ s do acc + worddata.e,
acc

function noargs(s:seq.symbol) int if isempty.s then 0 else value.1#s

function binary(a:seq.symbol, op:seq.word, b:seq.symbol) seq.symbol
a + b + symbol(internalmod, op, typeint, typeint, typeint)

function strExp(
code:seq.symbol
, str:seq.word
, forcecode:boolean
, expcode:seq.symbol
) seq.symbol
let code0 =
 if isempty.str then code
 else if isempty.code then [Words.str]
 else code + Words.str + catStringOp
let code1 = if forcecode ∧ isempty.code0 then [Words.""] else code0,
if isempty.expcode then code1 else code1 + expcode + catStringOp

function catStringOp symbol
symbol(moduleref("* seq", typeword), "+", [seqof.typeword, seqof.typeword], seqof.typeword)

function mergeText(a:seq.symbol, b:seq.symbol) seq.symbol
if not.isempty.a ∧ not.isempty.b then a + b + symbol(internalmod, "$mergecode", typeint, typeint, typeint)
else a + b

Function forbody(vars:seq.symbol, exitexp:seq.symbol, forbody:seq.symbol) seq.symbol
let n = value.1#vars
let textvars = subseq(vars, 2, n + 1)
let codevars = vars << (n + 1) >> (if worddata.1^vars = "." then 1 else 0)
let noseq = name.1^textvars ∈ ".",
codevars
 + exitexp
 + forbody
 + Words.worddata.textvars
 + symbol(
 internalmod
 , "$fortext"
 , constantseq(n - 1, typeint)
  + (if noseq then empty:seq.mytype else [typeint])
  + typeboolean
  + [typeint]
  + seqof.typeword
 , typeint
)

function forseq($0:seq.symbol, $1:seq.symbol, $2:seq.symbol) seq.symbol
[Lit(1 + noargs.$0)]
 + subseq($0, 2, 1 + noargs.$0)
 + $1
 + $0 << (1 + noargs.$0)
 + $2

function PEGgen(seqElementType:word, attributeType:seq.symbol) seq.boolean
{wordmap: carrot 1#"^", slash slash, dq 1#dq, 1#" $"}
[
 "Parser function Name (FPL) Type Declare' E" = mergeText($.4, $.5)
 , "/ function Name Type Declare' E" = mergeText($.3, $.4)
 , "/ Function Name (FPL) Type Declare' E" = mergeText($.4, $.5)
 , "/ Function Name Type Declare' E" = mergeText($.3, $.4)
 , "String dq String' dq" = strExp($.1, "", true, empty:seq.symbol)
 , "* String' carrot (E)" = strExp($.0, "", true, $.1)
 , "/ carrot" = strExp($.0, "^", false, empty:seq.symbol)
 , "/ str2" = strExp($.0, worddata.$.1, false, empty:seq.symbol)
 , "+str2 ! dq ! carrot any" = /All
 , "E Or" = $.1
 , "* EL', E" = [Lit(1 + noargs.$.0)] + $.0 << 1 + $.1
 , "Or And Or'" = $.1 + $.2
 , "* Or' ∨ And" = binary($.0, "∨", $.1)
 , "/ /or And" = binary($.0, "∨", $.1)
 , "/ ⊻ And" = binary($.0, "⊻", $.1)
 , "And Compare And'" = $.1 + $.2
 , "* And' ∧ Compare" = binary($.0, "∧", $.1)
 , "/ /and Compare" = binary($.0, "∧", $.1)
 , "Compare Sum Compare'" = $.1 + $.2
 , "* Compare' = Sum" = binary($.0, "=", $.1)
 , "/ ≠ Sum" = binary($.0, "≠", $.1)
 , "/ > Sum" = binary($.0, ">", $.1)
 , "/ < Sum" = binary($.0, "<", $.1)
 , "/ >1 Sum" = binary($.0, ">1", $.1)
 , "/ >2 Sum" = binary($.0, ">2", $.1)
 , "/ ≥ Sum" = binary($.0, "≥", $.1)
 , "/ /ge Sum" = binary($.0, "≥", $.1)
 , "/ ≤ Sum" = binary($.0, "≤", $.1)
 , "/ /le Sum" = binary($.0, "≤", $.1)
 , "/ /ne Sum" = binary($.0, "≠", $.1)
 , "Sum Product Sum'" = $.1 + $.2
 , "* Sum'-Product" = binary($.0, "-", $.1)
 , "/+Product" = binary($.0, "+", $.1)
 , "/ ∈ Product" = binary($.0, "∈", $.1)
 , "/ /in Product" = binary($.0, "∈", $.1)
 , "/ ∉ Product" = binary($.0, "∉", $.1)
 , "/ /nin Product" = binary($.0, "∉", $.1)
 , "Product Unary Product'" = $.1 + $.2
 , "* Product' * Unary" = binary($.0, "*", $.1)
 , "/ >> Unary" = binary($.0, ">>", $.1)
 , "/ << Unary" = binary($.0, "<<", $.1)
 , "/ slash Unary" = binary($.0, [slash], $.1)
 , "/ mod Unary" = binary($.0, "mod", $.1)
 , "/ ∩ Unary" = binary($.0, "∩", $.1)
 , "/ ∪ Unary" = binary($.0, "∪", $.1)
 , "/ /cap Unary" = binary($.0, "∩", $.1)
 , "/ /cup Unary" = binary($.0, "∪", $.1)
 , "/ \ Unary" = binary($.0, "\", $.1)
 , "Unary-Unary" = $.1 + symbol(internalmod, "-", typeint, typeint)
 , "/ Id.Unary" = $.2 + symbol(internalmod, worddata.1#$.1, typeint, typeint)
 , "/ {N} Unary"
 = (if isempty.$.1 then [Words.""] else $.1)
  + $.2
  + symbol(internalmod, "{", seqof.typeword, typeint, typeint)
 , "/ Power" = $.1
 , "Power Atom Power'" = $.1 + $.2
 , "* Power'#Unary" = binary($.0, "#", $.1)
 , "/^Unary" = binary($.0, "^", $.1)
 , "Atom (E)" = $.1 + symbol(internalmod, "(", typeint, typeint)
 , "/ [E EL']" = $.1 + $.2 << 1 + Sequence(typeint, 1 + noargs.$.2)
 , "/ String" = $.1
 , "/ Declare Declare' E" = mergeText(mergeText($.1, $.2), $.3)
 , "/ if E then E IF else E"
 = [Start.typeint] + $.1 + Br2(1, 2) + $.2 + Exit + $.3 + $.4 + EndBlock
 , "/ Name (E EL')"
 = $.2
  + $.3 << 1
  + symbol(
  internalmod
  , [merge.worddata.$.1]
  , constantseq(1 + noargs.$.3, typeint)
  , if n.worddata.$.1 > 1 then compoundNameType else typeint
 )
 , "/ Name"
 = [Local(merge.worddata.$.1, if n.worddata.$.1 > 1 then compoundNameType else typeint, 0)]
 , "Name Id:Type" = $.1 + Words.":" + $.2
 , "/ Id" = $.1
 , "Id !, ! [! (!] !) !:!.! dq any" = $.1
 , "comma?," = $.0
 , "/" = $.0
 , "* IF else if E then E" = $.0 + $.1 + Br2(1, 2) + $.2 + Exit
 , "Type Id.Type" = $.1 + Words."." + $.2
 , "/ Id" = $.1
 , "Declare let any = E comma?" = $.2 + Define(name.1#$.1, 1)
 , "/ assert E report E comma?"
 = $.1 + $.2 + symbol(internalmod, "$assert", typeboolean, seqof.typeword, typeint)
 , "/ {N} comma?"
 = $.0 + Words.worddata.$.1 + symbol(internalmod, "{", seqof.typeword, typeint)
 , "/ for ForDeclare do E comma?" = forbody($.1, [Littrue], $.2)
 , "/ for ForDeclare while E do E comma?" = forbody($.1, $.2, $.3)
 , "ForDeclare AccumList, any ∈ E" = forseq($.1, $.2, $.3)
 , "/ AccumList, any /in E" = forseq($.1, $.2, $.3)
 , "/ AccumList" = forseq($.1, [Words."."], [Words."."])
 , "AccumList ! while any = E AccumList'"
 = [Lit(1 + noargs.$.3)]
  + $.1
  + subseq($.3, 2, 1 + noargs.$.3)
  + $.2
  + $.3 << (1 + noargs.$.3)
 , "* AccumList', any = E" = forseq($.0, $.1, $.2)
 , "* Declare' Declare" = mergeText($.0, $.1)
 , "FPL FP FPL'" = $.1
 , "* FPL', FP" = $.1
 , "FP any:Type" = empty:seq.symbol
 , "/ Type" = empty:seq.symbol
 , "* N {N}" = /All
 , "/ !} any" = /All
]

<<<< Below is auto generated code >>>>

/br Non-terminals:AccumList AccumList' And And' Atom Compare Compare' Declare Declare' E EL' FP FPL FPL' ForDeclare IF Id N Name Or Or' Parser Power Power' Product Product' String String' Sum Sum' Type Unary comma? str2
/br Terminals:#() *+,-./and /cap /cup /ge /in /le /ne /nin /or:< << = > >1 >2 >> Function [\]^any assert carrot do dq else for function if let mod report slash then while {} ∈ ∉ ∧ ∨ ∩ ∪ ≠ ≤ ≥ ⊻
/br Parser ← function Name (FPL) Type Declare' E / function Name Type Declare' E / Function Name (FPL) Type Declare' E / Function Name Type Declare' E
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
/br * Compare' ← = Sum / ≠ Sum / > Sum / < Sum / >1 Sum / >2 Sum / ≥ Sum / /ge Sum / ≤ Sum / /le Sum / /ne Sum
/br Sum ← Product Sum'
/br * Sum' ←-Product /+Product / ∈ Product / /in Product / ∉ Product / /nin Product
/br Product ← Unary Product'
/br * Product' ← * Unary / >> Unary / << Unary / slash Unary / mod Unary / ∩ Unary / ∪ Unary / /cap Unary / /cup Unary / \ Unary
/br Unary ←-Unary / Id.Unary / {N} Unary / Power
/br Power ← Atom Power'
/br * Power' ←#Unary /^Unary
/br Atom ← (E) / [E EL'] / String / Declare Declare' E / if E then E IF else E / Name (E EL') / Name
/br Name ← Id:Type / Id
/br Id ← !, ! [! (!] !) !:!.! dq any
/br comma? ←, /
/br * IF ← else if E then E
/br Type ← Id.Type / Id
/br Declare ← let any = E comma? / assert E report E comma? / {N} comma? / for ForDeclare do E comma? / for ForDeclare while E do E comma?
/br ForDeclare ← AccumList, any ∈ E / AccumList, any /in E / AccumList
/br AccumList ← ! while any = E AccumList'
/br * AccumList' ←, any = E
/br * Declare' ← Declare
/br FPL ← FP FPL'
/br * FPL' ←, FP
/br FP ← any:Type / Type
/br * N ← {N} / !} any

function action(partno:int, R:seq.seq.symbol) seq.symbol
if partno = 2 then mergeText(2^R, 1^R)
else if partno = 3 then mergeText(2^R, 1^R)
else if partno = 4 then mergeText(2^R, 1^R)
else if partno = 5 then mergeText(2^R, 1^R)
else if partno = 6 then strExp(1^R, "", true, empty:seq.symbol)
else if partno = 7 then strExp(2^R, "", true, 1^R)
else if partno = 8 then strExp(1^R, "^", false, empty:seq.symbol)
else if partno = 9 then strExp(2^R, worddata.1^R, false, empty:seq.symbol)
else if partno = 11 then 1^R
else if partno = 12 then [Lit(1 + noargs.2^R)] + 2^R << 1 + 1^R
else if partno = 13 then 2^R + 1^R
else if partno = 14 then binary(2^R, "∨", 1^R)
else if partno = 15 then binary(2^R, "∨", 1^R)
else if partno = 16 then binary(2^R, "⊻", 1^R)
else if partno = 17 then 2^R + 1^R
else if partno = 18 then binary(2^R, "∧", 1^R)
else if partno = 19 then binary(2^R, "∧", 1^R)
else if partno = 20 then 2^R + 1^R
else if partno = 21 then binary(2^R, "=", 1^R)
else if partno = 22 then binary(2^R, "≠", 1^R)
else if partno = 23 then binary(2^R, ">", 1^R)
else if partno = 24 then binary(2^R, "<", 1^R)
else if partno = 25 then binary(2^R, ">1", 1^R)
else if partno = 26 then binary(2^R, ">2", 1^R)
else if partno = 27 then binary(2^R, "≥", 1^R)
else if partno = 28 then binary(2^R, "≥", 1^R)
else if partno = 29 then binary(2^R, "≤", 1^R)
else if partno = 30 then binary(2^R, "≤", 1^R)
else if partno = 31 then binary(2^R, "≠", 1^R)
else if partno = 32 then 2^R + 1^R
else if partno = 33 then binary(2^R, "-", 1^R)
else if partno = 34 then binary(2^R, "+", 1^R)
else if partno = 35 then binary(2^R, "∈", 1^R)
else if partno = 36 then binary(2^R, "∈", 1^R)
else if partno = 37 then binary(2^R, "∉", 1^R)
else if partno = 38 then binary(2^R, "∉", 1^R)
else if partno = 39 then 2^R + 1^R
else if partno = 40 then binary(2^R, "*", 1^R)
else if partno = 41 then binary(2^R, ">>", 1^R)
else if partno = 42 then binary(2^R, "<<", 1^R)
else if partno = 43 then binary(2^R, [slash], 1^R)
else if partno = 44 then binary(2^R, "mod", 1^R)
else if partno = 45 then binary(2^R, "∩", 1^R)
else if partno = 46 then binary(2^R, "∪", 1^R)
else if partno = 47 then binary(2^R, "∩", 1^R)
else if partno = 48 then binary(2^R, "∪", 1^R)
else if partno = 49 then binary(2^R, "\", 1^R)
else if partno = 50 then 1^R + symbol(internalmod, "-", typeint, typeint)
else if partno = 51 then 1^R + symbol(internalmod, worddata.1#(2^R), typeint, typeint)
else if partno = 52 then
 (if isempty.2^R then [Words.""] else 2^R)
  + 1^R
  + symbol(internalmod, "{", seqof.typeword, typeint, typeint)
else if partno = 53 then 1^R
else if partno = 54 then 2^R + 1^R
else if partno = 55 then binary(2^R, "#", 1^R)
else if partno = 56 then binary(2^R, "^", 1^R)
else if partno = 57 then 1^R + symbol(internalmod, "(", typeint, typeint)
else if partno = 58 then 2^R + 1^R << 1 + Sequence(typeint, 1 + noargs.1^R)
else if partno = 59 then 1^R
else if partno = 60 then mergeText(mergeText(3^R, 2^R), 1^R)
else if partno = 61 then [Start.typeint] + 4^R + Br2(1, 2) + 3^R + Exit + 2^R + 1^R + EndBlock
else if partno = 62 then
 2^R
  + 1^R << 1
  + symbol(
  internalmod
  , [merge.worddata.3^R]
  , constantseq(1 + noargs.1^R, typeint)
  , if n.worddata.3^R > 1 then compoundNameType else typeint
 )
else if partno = 63 then [Local(merge.worddata.1^R, if n.worddata.1^R > 1 then compoundNameType else typeint, 0)]
else if partno = 64 then 2^R + Words.":" + 1^R
else if partno = 65 then 1^R
else if partno = 66 then 1^R
else if partno = 67 then 1^R
else if partno = 68 then 1^R
else if partno = 69 then 3^R + 2^R + Br2(1, 2) + 1^R + Exit
else if partno = 70 then 2^R + Words."." + 1^R
else if partno = 71 then 1^R
else if partno = 72 then 2^R + Define(name.1#(3^R), 1)
else if partno = 73 then 3^R + 2^R + symbol(internalmod, "$assert", typeboolean, seqof.typeword, typeint)
else if partno = 74 then 3^R + Words.worddata.2^R + symbol(internalmod, "{", seqof.typeword, typeint)
else if partno = 75 then forbody(3^R, [Littrue], 2^R)
else if partno = 76 then forbody(4^R, 3^R, 2^R)
else if partno = 77 then forseq(3^R, 2^R, 1^R)
else if partno = 78 then forseq(3^R, 2^R, 1^R)
else if partno = 79 then forseq(1^R, [Words."."], [Words."."])
else if partno = 80 then
 [Lit(1 + noargs.1^R)]
  + 3^R
  + subseq(1^R, 2, 1 + noargs.1^R)
  + 2^R
  + 1^R << (1 + noargs.1^R)
else if partno = 81 then forseq(3^R, 2^R, 1^R)
else if partno = 82 then mergeText(2^R, 1^R)
else if partno = 83 then 2^R
else if partno = 84 then 1^R
else if partno = 85 then empty:seq.symbol
else if partno = 86 then empty:seq.symbol
else 1#R

function mytable seq.tableEntry
[
 {1} tableEntry(NT.T'.2, 1#"?", Match, Failure, "")
 , {2} tableEntry(T', 1#"function", NT.3, T'.15, "")
 , {3} tableEntry(NT.157, 1#"Name", T'.4, T'.15, "")
 , {4} tableEntry(T', 1#"(", NT.5, NT.12, "")
 , {5} tableEntry(NT.227, 1#"FPL", T.6, T'.10, "")
 , {6} tableEntry(T, 1#")", NT.7, T'.10, "")
 , {7} tableEntry(NT.176, 1#"Type", NT.8, T'.10, "")
 , {8} tableEntry(NT.226, 1#"Declare'", NT.9, T'.10, "")
 , {9} tableEntry(NT.40, 1#"E", Reduce.2, T'.10, "")
 , {10} tableEntry(T', 1#"function", NT.11, T'.15, "")
 , {11} tableEntry(NT.157, 1#"Name", NT.12, T'.15, "")
 , {12} tableEntry(NT.176, 1#"Type", NT.13, T'.15, "")
 , {13} tableEntry(NT.226, 1#"Declare'", NT.14, T'.15, "")
 , {14} tableEntry(NT.40, 1#"E", Reduce.3, T'.15, "")
 , {15} tableEntry(T', 1#"Function", NT.16, Fail, "")
 , {16} tableEntry(NT.157, 1#"Name", T'.17, Fail, "")
 , {17} tableEntry(T', 1#"(", NT.18, NT.25, "")
 , {18} tableEntry(NT.227, 1#"FPL", T.19, T.23, "")
 , {19} tableEntry(T, 1#")", NT.20, T.23, "")
 , {20} tableEntry(NT.176, 1#"Type", NT.21, T.23, "")
 , {21} tableEntry(NT.226, 1#"Declare'", NT.22, T.23, "")
 , {22} tableEntry(NT.40, 1#"E", Reduce.4, T.23, "")
 , {23} tableEntry(T, 1#"Function", NT.24, Fail, "")
 , {24} tableEntry(NT.157, 1#"Name", NT.25, Fail, "")
 , {25} tableEntry(NT.176, 1#"Type", NT.26, Fail, "")
 , {26} tableEntry(NT.226, 1#"Declare'", NT.27, Fail, "")
 , {27} tableEntry(NT.40, 1#"E", Reduce.5, Fail, "")
 , {28} tableEntry(T, 1#dq, NT.29, Fail, "")
 , {29} tableEntry(NT.T'.31, 1#"String'", T.30, Fail, "")
 , {30} tableEntry(T, 1#dq, Reduce.6, Fail, "")
 , {31} tableEntry(T', 1#"^", T.32, NT.36, "")
 , {32} tableEntry(T, 1#"(", NT.33, T'.35, "")
 , {33} tableEntry(NT.40, 1#"E", T.34, T'.35, "")
 , {34} tableEntry(T, 1#")", Reduce*(7, T'.31), T'.35, "")
 , {35} tableEntry(T', 1#"^", Reduce*(8, T'.31), NT.36, "")
 , {36} tableEntry(NT.!T.37, 1#"str2", Reduce*(9, T'.31), Success*, "")
 , {37} tableEntry(!T, 1#dq, Fail, !T.38, "")
 , {38} tableEntry(!T, 1#"^", Fail, MatchAny.39, "")
 , {39} tableEntry(MatchAny, 1#"?", Discard*.!T.240, Fail, "")
 , {40} tableEntry(NT.43, 1#"Or", Reduce.11, Fail, "")
 , {41} tableEntry(T, 1#",", NT.42, Success*, "")
 , {42} tableEntry(NT.40, 1#"E", Reduce*(12, T.41), Success*, "")
 , {43} tableEntry(NT.51, 1#"And", NT.44, Fail, "")
 , {44} tableEntry(NT.T'.45, 1#"Or'", Reduce.13, Fail, "")
 , {45} tableEntry(T', 1#"∨", NT.46, T'.47, "")
 , {46} tableEntry(NT.51, 1#"And", Reduce*(14, T'.45), T'.47, "")
 , {47} tableEntry(T', 1#"/or", NT.48, T.49, "")
 , {48} tableEntry(NT.51, 1#"And", Reduce*(15, T'.45), T.49, "")
 , {49} tableEntry(T, 1#"⊻", NT.50, Success*, "")
 , {50} tableEntry(NT.51, 1#"And", Reduce*(16, T'.45), Success*, "")
 , {51} tableEntry(NT.57, 1#"Compare", NT.52, Fail, "")
 , {52} tableEntry(NT.T'.53, 1#"And'", Reduce.17, Fail, "")
 , {53} tableEntry(T', 1#"∧", NT.54, T.55, "")
 , {54} tableEntry(NT.57, 1#"Compare", Reduce*(18, T'.53), T.55, "")
 , {55} tableEntry(T, 1#"/and", NT.56, Success*, "")
 , {56} tableEntry(NT.57, 1#"Compare", Reduce*(19, T'.53), Success*, "")
 , {57} tableEntry(NT.81, 1#"Sum", NT.58, Fail, "")
 , {58} tableEntry(NT.T'.59, 1#"Compare'", Reduce.20, Fail, "")
 , {59} tableEntry(T', 1#"=", NT.60, T'.61, "")
 , {60} tableEntry(NT.81, 1#"Sum", Reduce*(21, T'.59), T'.61, "")
 , {61} tableEntry(T', 1#"≠", NT.62, T'.63, "")
 , {62} tableEntry(NT.81, 1#"Sum", Reduce*(22, T'.59), T'.63, "")
 , {63} tableEntry(T', 1#">", NT.64, T'.65, "")
 , {64} tableEntry(NT.81, 1#"Sum", Reduce*(23, T'.59), T'.65, "")
 , {65} tableEntry(T', 1#"<", NT.66, T'.67, "")
 , {66} tableEntry(NT.81, 1#"Sum", Reduce*(24, T'.59), T'.67, "")
 , {67} tableEntry(T', 1#">1", NT.68, T'.69, "")
 , {68} tableEntry(NT.81, 1#"Sum", Reduce*(25, T'.59), T'.69, "")
 , {69} tableEntry(T', 1#">2", NT.70, T'.71, "")
 , {70} tableEntry(NT.81, 1#"Sum", Reduce*(26, T'.59), T'.71, "")
 , {71} tableEntry(T', 1#"≥", NT.72, T'.73, "")
 , {72} tableEntry(NT.81, 1#"Sum", Reduce*(27, T'.59), T'.73, "")
 , {73} tableEntry(T', 1#"/ge", NT.74, T'.75, "")
 , {74} tableEntry(NT.81, 1#"Sum", Reduce*(28, T'.59), T'.75, "")
 , {75} tableEntry(T', 1#"≤", NT.76, T'.77, "")
 , {76} tableEntry(NT.81, 1#"Sum", Reduce*(29, T'.59), T'.77, "")
 , {77} tableEntry(T', 1#"/le", NT.78, T.79, "")
 , {78} tableEntry(NT.81, 1#"Sum", Reduce*(30, T'.59), T.79, "")
 , {79} tableEntry(T, 1#"/ne", NT.80, Success*, "")
 , {80} tableEntry(NT.81, 1#"Sum", Reduce*(31, T'.59), Success*, "")
 , {81} tableEntry(NT.95, 1#"Product", NT.82, Fail, "")
 , {82} tableEntry(NT.T'.83, 1#"Sum'", Reduce.32, Fail, "")
 , {83} tableEntry(T', 1#"-", NT.84, T'.85, "")
 , {84} tableEntry(NT.95, 1#"Product", Reduce*(33, T'.83), T'.85, "")
 , {85} tableEntry(T', 1#"+", NT.86, T'.87, "")
 , {86} tableEntry(NT.95, 1#"Product", Reduce*(34, T'.83), T'.87, "")
 , {87} tableEntry(T', 1#"∈", NT.88, T'.89, "")
 , {88} tableEntry(NT.95, 1#"Product", Reduce*(35, T'.83), T'.89, "")
 , {89} tableEntry(T', 1#"/in", NT.90, T'.91, "")
 , {90} tableEntry(NT.95, 1#"Product", Reduce*(36, T'.83), T'.91, "")
 , {91} tableEntry(T', 1#"∉", NT.92, T.93, "")
 , {92} tableEntry(NT.95, 1#"Product", Reduce*(37, T'.83), T.93, "")
 , {93} tableEntry(T, 1#"/nin", NT.94, Success*, "")
 , {94} tableEntry(NT.95, 1#"Product", Reduce*(38, T'.83), Success*, "")
 , {95} tableEntry(NT.T'.117, 1#"Unary", NT.96, Fail, "")
 , {96} tableEntry(NT.T'.97, 1#"Product'", Reduce.39, Fail, "")
 , {97} tableEntry(T', 1#"*", NT.98, T'.99, "")
 , {98} tableEntry(NT.T'.117, 1#"Unary", Reduce*(40, T'.97), T'.99, "")
 , {99} tableEntry(T', 1#">>", NT.100, T'.101, "")
 , {100} tableEntry(NT.T'.117, 1#"Unary", Reduce*(41, T'.97), T'.101, "")
 , {101} tableEntry(T', 1#"<<", NT.102, T'.103, "")
 , {102} tableEntry(NT.T'.117, 1#"Unary", Reduce*(42, T'.97), T'.103, "")
 , {103} tableEntry(T', slash, NT.104, T'.105, "")
 , {104} tableEntry(NT.T'.117, 1#"Unary", Reduce*(43, T'.97), T'.105, "")
 , {105} tableEntry(T', 1#"mod", NT.106, T'.107, "")
 , {106} tableEntry(NT.T'.117, 1#"Unary", Reduce*(44, T'.97), T'.107, "")
 , {107} tableEntry(T', 1#"∩", NT.108, T'.109, "")
 , {108} tableEntry(NT.T'.117, 1#"Unary", Reduce*(45, T'.97), T'.109, "")
 , {109} tableEntry(T', 1#"∪", NT.110, T'.111, "")
 , {110} tableEntry(NT.T'.117, 1#"Unary", Reduce*(46, T'.97), T'.111, "")
 , {111} tableEntry(T', 1#"/cap", NT.112, T'.113, "")
 , {112} tableEntry(NT.T'.117, 1#"Unary", Reduce*(47, T'.97), T'.113, "")
 , {113} tableEntry(T', 1#"/cup", NT.114, T.115, "")
 , {114} tableEntry(NT.T'.117, 1#"Unary", Reduce*(48, T'.97), T.115, "")
 , {115} tableEntry(T, 1#"\", NT.116, Success*, "")
 , {116} tableEntry(NT.T'.117, 1#"Unary", Reduce*(49, T'.97), Success*, "")
 , {117} tableEntry(T', 1#"-", NT.118, NT.119, "")
 , {118} tableEntry(NT.T'.117, 1#"Unary", Reduce.50, NT.119, "")
 , {119} tableEntry(NT.!T.161, 1#"Id", T.120, T'.122, "")
 , {120} tableEntry(T, 1#".", NT.121, T'.122, "")
 , {121} tableEntry(NT.T'.117, 1#"Unary", Reduce.51, T'.122, "")
 , {122} tableEntry(T', 1#"{", NT.123, NT.126, "")
 , {123} tableEntry(NT.T.235, 1#"N", T.124, NT.126, "")
 , {124} tableEntry(T, 1#"}", NT.125, NT.126, "")
 , {125} tableEntry(NT.T'.117, 1#"Unary", Reduce.52, NT.126, "")
 , {126} tableEntry(NT.127, 1#"Power", Reduce.53, Fail, "")
 , {127} tableEntry(NT.T'.133, 1#"Atom", NT.128, Fail, "")
 , {128} tableEntry(NT.T'.129, 1#"Power'", Reduce.54, Fail, "")
 , {129} tableEntry(T', 1#"#", NT.130, T.131, "")
 , {130} tableEntry(NT.T'.117, 1#"Unary", Reduce*(55, T'.129), T.131, "")
 , {131} tableEntry(T, 1#"^", NT.132, Success*, "")
 , {132} tableEntry(NT.T'.117, 1#"Unary", Reduce*(56, T'.129), Success*, "")
 , {133} tableEntry(T', 1#"(", NT.134, T'.136, "")
 , {134} tableEntry(NT.40, 1#"E", T.135, T'.136, "")
 , {135} tableEntry(T, 1#")", Reduce.57, T'.136, "")
 , {136} tableEntry(T', 1#"[", NT.137, NT.140, "")
 , {137} tableEntry(NT.40, 1#"E", NT.138, NT.140, "")
 , {138} tableEntry(NT.T.41, 1#"EL'", T.139, NT.140, "")
 , {139} tableEntry(T, 1#"]", Reduce.58, NT.140, "")
 , {140} tableEntry(NT.T.28, 1#"String", Reduce.59, NT.141, "")
 , {141} tableEntry(NT.T'.180, 1#"Declare", NT.142, T'.144, "")
 , {142} tableEntry(NT.226, 1#"Declare'", NT.143, T'.144, "")
 , {143} tableEntry(NT.40, 1#"E", Reduce.60, T'.144, "")
 , {144} tableEntry(T', 1#"if", NT.145, NT.151, "")
 , {145} tableEntry(NT.40, 1#"E", T.146, NT.151, "")
 , {146} tableEntry(T, 1#"then", NT.147, NT.151, "")
 , {147} tableEntry(NT.40, 1#"E", NT.148, NT.151, "")
 , {148} tableEntry(NT.T.171, 1#"IF", T.149, NT.151, "")
 , {149} tableEntry(T, 1#"else", NT.150, NT.151, "")
 , {150} tableEntry(NT.40, 1#"E", Reduce.61, NT.151, "")
 , {151} tableEntry(NT.157, 1#"Name", T.152, Fail, "")
 , {152} tableEntry(T, 1#"(", NT.153, NT.156, "")
 , {153} tableEntry(NT.40, 1#"E", NT.154, NT.156, "")
 , {154} tableEntry(NT.T.41, 1#"EL'", T.155, NT.156, "")
 , {155} tableEntry(T, 1#")", Reduce.62, NT.156, "")
 , {156} tableEntry(NT.157, 1#"Name", Reduce.63, Fail, "")
 , {157} tableEntry(NT.!T.161, 1#"Id", T.158, Fail, "")
 , {158} tableEntry(T, 1#":", NT.159, NT.160, "")
 , {159} tableEntry(NT.176, 1#"Type", Reduce.64, NT.160, "")
 , {160} tableEntry(NT.!T.161, 1#"Id", Reduce.65, Fail, "")
 , {161} tableEntry(!T, 1#",", Fail, !T.162, "")
 , {162} tableEntry(!T, 1#"[", Fail, !T.163, "")
 , {163} tableEntry(!T, 1#"(", Fail, !T.164, "")
 , {164} tableEntry(!T, 1#"]", Fail, !T.165, "")
 , {165} tableEntry(!T, 1#")", Fail, !T.166, "")
 , {166} tableEntry(!T, 1#":", Fail, !T.167, "")
 , {167} tableEntry(!T, 1#".", Fail, !T.168, "")
 , {168} tableEntry(!T, 1#dq, Fail, MatchAny.169, "")
 , {169} tableEntry(MatchAny, 1#"?", Reduce.66, Fail, "")
 , {170} tableEntry(T, 1#",", Reduce.67, Reduce.68, "")
 , {171} tableEntry(T, 1#"else", T.172, Success*, "")
 , {172} tableEntry(T, 1#"if", NT.173, Success*, "")
 , {173} tableEntry(NT.40, 1#"E", T.174, Success*, "")
 , {174} tableEntry(T, 1#"then", NT.175, Success*, "")
 , {175} tableEntry(NT.40, 1#"E", Reduce*(69, T.171), Success*, "")
 , {176} tableEntry(NT.!T.161, 1#"Id", T.177, Fail, "")
 , {177} tableEntry(T, 1#".", NT.178, NT.179, "")
 , {178} tableEntry(NT.176, 1#"Type", Reduce.70, NT.179, "")
 , {179} tableEntry(NT.!T.161, 1#"Id", Reduce.71, Fail, "")
 , {180} tableEntry(T', 1#"let", MatchAny.181, T'.185, "")
 , {181} tableEntry(MatchAny, 1#"?", T.182, T'.185, "")
 , {182} tableEntry(T, 1#"=", NT.183, T'.185, "")
 , {183} tableEntry(NT.40, 1#"E", NT.184, T'.185, "")
 , {184} tableEntry(NT.T.170, 1#"comma?", Reduce.72, T'.185, "")
 , {185} tableEntry(T', 1#"assert", NT.186, T'.190, "")
 , {186} tableEntry(NT.40, 1#"E", T.187, T'.190, "")
 , {187} tableEntry(T, 1#"report", NT.188, T'.190, "")
 , {188} tableEntry(NT.40, 1#"E", NT.189, T'.190, "")
 , {189} tableEntry(NT.T.170, 1#"comma?", Reduce.73, T'.190, "")
 , {190} tableEntry(T', 1#"{", NT.191, T'.194, "")
 , {191} tableEntry(NT.T.235, 1#"N", T.192, T'.194, "")
 , {192} tableEntry(T, 1#"}", NT.193, T'.194, "")
 , {193} tableEntry(NT.T.170, 1#"comma?", Reduce.74, T'.194, "")
 , {194} tableEntry(T', 1#"for", NT.195, Fail, "")
 , {195} tableEntry(NT.206, 1#"ForDeclare", T'.196, Fail, "")
 , {196} tableEntry(T', 1#"do", NT.197, T.201, "")
 , {197} tableEntry(NT.40, 1#"E", NT.198, T.199, "")
 , {198} tableEntry(NT.T.170, 1#"comma?", Reduce.75, T.199, "")
 , {199} tableEntry(T, 1#"for", NT.200, Fail, "")
 , {200} tableEntry(NT.206, 1#"ForDeclare", T.201, Fail, "")
 , {201} tableEntry(T, 1#"while", NT.202, Fail, "")
 , {202} tableEntry(NT.40, 1#"E", T.203, Fail, "")
 , {203} tableEntry(T, 1#"do", NT.204, Fail, "")
 , {204} tableEntry(NT.40, 1#"E", NT.205, Fail, "")
 , {205} tableEntry(NT.T.170, 1#"comma?", Reduce.76, Fail, "")
 , {206} tableEntry(NT.!T.217, 1#"AccumList", T'.207, Fail, "")
 , {207} tableEntry(T', 1#",", MatchAny.208, T.212, "")
 , {208} tableEntry(MatchAny, 1#"?", T'.209, NT.211, "")
 , {209} tableEntry(T', 1#"∈", NT.210, T.214, "")
 , {210} tableEntry(NT.40, 1#"E", Reduce.77, NT.211, "")
 , {211} tableEntry(NT.!T.217, 1#"AccumList", T.212, Fail, "")
 , {212} tableEntry(T, 1#",", MatchAny.213, NT.216, "")
 , {213} tableEntry(MatchAny, 1#"?", T.214, NT.216, "")
 , {214} tableEntry(T, 1#"/in", NT.215, NT.216, "")
 , {215} tableEntry(NT.40, 1#"E", Reduce.78, NT.216, "")
 , {216} tableEntry(NT.!T.217, 1#"AccumList", Reduce.79, Fail, "")
 , {217} tableEntry(!T, 1#"while", Fail, MatchAny.218, "")
 , {218} tableEntry(MatchAny, 1#"?", T.219, Fail, "")
 , {219} tableEntry(T, 1#"=", NT.220, Fail, "")
 , {220} tableEntry(NT.40, 1#"E", NT.221, Fail, "")
 , {221} tableEntry(NT.T.222, 1#"AccumList'", Reduce.80, Fail, "")
 , {222} tableEntry(T, 1#",", MatchAny.223, Success*, "")
 , {223} tableEntry(MatchAny, 1#"?", T.224, Success*, "")
 , {224} tableEntry(T, 1#"=", NT.225, Success*, "")
 , {225} tableEntry(NT.40, 1#"E", Reduce*(81, T.222), Success*, "")
 , {226} tableEntry(NT.T'.180, 1#"Declare", Reduce*(82, NT.226), Success*, "")
 , {227} tableEntry(NT.MatchAny.231, 1#"FP", NT.228, Fail, "")
 , {228} tableEntry(NT.T.229, 1#"FPL'", Reduce.83, Fail, "")
 , {229} tableEntry(T, 1#",", NT.230, Success*, "")
 , {230} tableEntry(NT.MatchAny.231, 1#"FP", Reduce*(84, T.229), Success*, "")
 , {231} tableEntry(MatchAny, 1#"?", T.232, NT.234, "")
 , {232} tableEntry(T, 1#":", NT.233, NT.234, "")
 , {233} tableEntry(NT.176, 1#"Type", Reduce.85, NT.234, "")
 , {234} tableEntry(NT.176, 1#"Type", Reduce.86, Fail, "")
 , {235} tableEntry(T, 1#"{", NT.236, !T.238, "")
 , {236} tableEntry(NT.T.235, 1#"N", T.237, !T.238, "")
 , {237} tableEntry(T, 1#"}", Discard*.T.235, !T.238, "")
 , {238} tableEntry(!T, 1#"}", All, MatchAny.239, "")
 , {239} tableEntry(MatchAny, 1#"?", Discard*.T.235, All, "")
 , {240} tableEntry(!T, 1#dq, All, !T.241, "")
 , {241} tableEntry(!T, 1#"^", All, MatchAny.242, "")
 , {242} tableEntry(MatchAny, 1#"?", Discard*.!T.240, All, "")
]

function =(seq.word, seq.symbol) boolean true

function $(int) seq.symbol 1#empty:seq.seq.symbol

use standard

use seq.tableEntry

use otherseq.frame

use stack.frame

use otherseq.seq.symbol

use PEGrules

function place(r:resultType) int i.top.stk.r

type frame is
Sstate:state
, Fstate:state
, i:int
, result:seq.seq.symbol
, faili:int
, failresult:seq.seq.symbol

type resultType is stk:stack.frame

Function status(a:resultType) word
if Sstate.top.stk.a ≠ Match then 1#"Failed"
else if place.a = {length of input} faili.top.stk.a then 1#"Match"
else 1#"MatchPrefix"

Function result(a:resultType) seq.symbol 1^result.top.stk.a

function parse(myinput0:seq.word, initAttr:seq.symbol) resultType
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
  let att = [toAttribute(1^result, subseq(myinput, i.top, i - 1))],
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
  if inputi ≠ match.te then {fail} next(stk, Fstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)
  else next(stk, Sstate.te, i + 1, idxNB(myinput, i + 1), result, faili, failresult)
 else if actionState = !T then
  let te = idxNB(packedTable, index.state),
  if inputi = match.te then {fail} next(stk, Sstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)
  else next(stk, Fstate.te, i, inputi, result, faili, failresult)
 else if actionState = MatchAny then
  let te = idxNB(packedTable, index.state),
  if inputi = endMark then {fail} next(stk, Fstate.te, i, inputi, result, faili, failresult)
  else
   let reslt = result + toAttribute(1^result, [inputi])
   let ini = idxNB(myinput, i + 1),
   next(stk, Sstate.te, i + 1, ini, reslt, faili, failresult)
 else if actionState = T' then
  let te = idxNB(packedTable, index.state),
  if inputi = match.te then next(stk, Sstate.te, i + 1, idxNB(myinput, i + 1), result, faili, failresult)
  else next(stk, Fstate.te, i, inputi, result, faili, failresult)
 else
  {match non Terminal}
  let te = idxNB(packedTable, index.state)
  assert action.action.te ∈ [NT, NT*] report "PROBLEM PEG^(state)"
  let newstk = push(stk, frame(Sstate.te, Fstate.te, i, result, faili, failresult)),
  let tmp = [toAttribute(1^result, empty:seq.word)],
  next(newstk, nextState.action.te, i, inputi, tmp, i, tmp),
resultType.push(stk, frame(state, state, i, result, n.myinput, result)) 