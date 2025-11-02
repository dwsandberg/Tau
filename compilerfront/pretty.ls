Module pretty

use token

use seq.token

use file

use seq.file

use seq.filename

use seq1.mytype

use prettyR

use standard

use seq.symbol

use set.symbol

use symbol1

use set.symlink

use seq1.word

use seq.word

use seq.seq.word

use set.seq.word

use sort.seq.word

use sort.word

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

Function sortuse(b:seq.seq.word, prefix:seq.word) seq.seq.word
for a = empty:seq.seq.word, u ∈ b do a + reverse.u
for acc = empty:seq.seq.word, @e ∈ sort>alpha.toseq.asset.a
do acc + (prefix + reverse.@e),
acc

Function pretty(p:seq.word) seq.word pretty(p, true)

Function prettyNoChange(p:seq.word) seq.word pretty(p, false)

Function libsrc(m:midpoint, outfn:seq.filename) seq.file
let outname = outfn sub 1
for only = "", fn ∈ outfn
do if ext.fn ∈ "libsrc" then only + name.fn else only
for
 libname = "?" sub 1
 , all = ""
 , libtxt = ""
 , libs = empty:seq.file
 , p ∈ src.m << 1 + ["# File:+?"]
do
 if subseq(p, 1, 3) = "# File:" ∧ n.p > 4 then
  let newlibname = p sub 5,
  if newlibname = libname then next(newlibname, all, libtxt, libs)
  else
   let newlibs =
    if libname ∉ only ∨ isempty.libtxt then libs
    else libs + file(filename("+:(dirpath.outname)" + libname + ".libsrc"), libtxt),
   next(newlibname, all + "/p" + libtxt, p, newlibs)
 else
  let newtxt =
   if subseq(p, 1, 1)
   ∈ ["Function", "function", "Export", "type", "builtin", "Builtin", "unbound"] then prettyNoChange.p
   else escapeformat.p,
  next(libname, all, libtxt + "/p" + newtxt, libs),
[file(changeext(outname, "libsrc"), all)] + libs

function pretty(p:seq.word, change:boolean) seq.word
if p sub 1 ∈ "Function function" then
 assert opprec."+" sub 1 = 4 report "no prec specified"
 let r = parse(totokens.p, empty:seq.symbol),
 if status.r ∈ "Match MatchPrefix" then pretty(formatHeader.getheader.p, result.r, empty:set.symlink, change)
 else [status.r] + %.result.r
else if p sub 1 ∈ "Export unbound Builtin builtin" then
 let h = formatHeader.getheader.p
 let rest = p << (findindex(p, "{" sub 1) - 1),
 if width(h + rest) < maxwidth then h + rest else h + "/br" + rest
else if p sub 1 ∈ "type" then
 if width.p < maxwidth then p
 else
  for acc = subseq(p, 1, 3), e ∈ break(p << 3, ",", true)
  do acc + "/br" + e,
  acc
else p

function toAttribute(b:seq.symbol, tokens:seq.token) seq.symbol
for w = "", e ∈ tokens do w + toword.e,
if isempty.w then empty:seq.symbol else [Words.w]

function endMark token totoken.encodeword.[char.254]

function worddata(s:seq.symbol) seq.word
for acc = "", e ∈ s do acc + worddata.e,
acc

function noargs(s:seq.symbol) int if isempty.s then 0 else value.s sub 1

function binary(a:seq.symbol, firsttoken:token, b:seq.symbol) seq.symbol
let op = [toword.firsttoken],
a + b + symbol(internalmod, op, [typeint, typeint], typeint)

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
if not.isempty.a ∧ not.isempty.b then a + b + symbol(internalmod, "$mergecode", [typeint, typeint], typeint)
else a + b

Function forbody(vars:seq.symbol, exitexp:seq.symbol, forbody:seq.symbol) seq.symbol
let n = value.vars sub 1
let textvars = subseq(vars, 2, n + 1)
let codevars = vars << (n + 1) >> (if worddata.vars sub n.vars = "." then 1 else 0)
let noseq = name.textvars sub n.textvars ∈ ".",
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

function firsttoken(r:resultType) token (input.r) sub faili.r

function colon seq.word ":"

function genPEG(
seqElementType:token
, attributeType:seq.symbol
, error:boolean
, rinfo:resultType
) seq.boolean
{wordmap: colon totoken.colon sub 1, dq totoken.dq sub 1, totoken." $" sub 1}
[
 "Parser function Name (FPL) Type Declare' E" = mergeText($.4, $.5)
 , "/ function Name Type Declare' E" = mergeText($.3, $.4)
 , "String dq String' dq" = strExp($.1, "", true, empty:seq.symbol)
 , "* String' colon (E)" = strExp($.0, "", true, $.1)
 , "/ colon" = strExp($.0, [toword.firsttoken.rinfo], false, empty:seq.symbol)
 , "/ str2" = strExp($.0, worddata.$.1, false, empty:seq.symbol)
 , "+str2 ! dq ! colon any" = /All
 , "E Or" = $.1
 , "* EL', E" = [Lit(1 + noargs.$.0)] + $.0 << 1 + $.1
 , "Or And Or'" = $.1 + $.2
 , "* Or' ∨ And" = binary($.0, firsttoken.rinfo, $.1)
 , "And Compare And'" = $.1 + $.2
 , "* And' ∧ Compare" = binary($.0, firsttoken.rinfo, $.1)
 , "Compare Sum Compare'" = $.1 + $.2
 , "* Compare' > Sum" = binary($.0, firsttoken.rinfo, $.1)
 , "Sum Product Sum'" = $.1 + $.2
 , "* Sum'+Product" = binary($.0, firsttoken.rinfo, $.1)
 , "Product Unary Product'" = $.1 + $.2
 , "* Product' * Unary" = binary($.0, firsttoken.rinfo, $.1)
 , "Unary-Unary" = $.1 + symbol(internalmod, [toword.firsttoken.rinfo], [typeint], typeint)
 , "/ Id.Unary" = $.2 + symbol(internalmod, worddata.($.1) sub 1, [typeint], typeint)
 , "/ {N} Unary"
 = (if isempty.$.1 then [Words.""] else $.1)
  + $.2
  + symbol(internalmod, "{", [seqof.typeword, typeint], typeint)
 , "/ Power" = $.1
 , "Power Atom Power'" = $.1 + $.2
 , "* Power' sub Unary" = binary($.0, firsttoken.rinfo, $.1)
 , "Atom (E)" = $.1 + symbol(internalmod, "(", [typeint], typeint)
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
 , "Declare let any = E comma?" = $.2 + Define(name.($.1) sub 1, 1)
 , "/ assert E report E comma?"
 = $.1 + $.2 + symbol(internalmod, "$assert", [typeboolean, seqof.typeword], typeint)
 , "/ {N} comma?"
 = $.0 + Words.worddata.$.1 + symbol(internalmod, "{", [seqof.typeword], typeint)
 , "/ for ForDeclare do E comma?" = forbody($.1, [Littrue], $.2)
 , "/ for ForDeclare while E do E comma?" = forbody($.1, $.2, $.3)
 , "ForDeclare AccumList, any ∈ E" = forseq($.1, $.2, $.3)
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
/br Terminals:() *+,-.:= > [] any assert colon do dq else for function if let report sub then while {} ∈ ∧ ∨
/br Parser ← function Name (FPL) Type Declare' E / function Name Type Declare' E
/br String ← dq String' dq
/br * String' ← colon (E) / colon / str2
/br+str2 ← ! dq ! colon any
/br E ← Or
/br * EL' ←, E
/br Or ← And Or'
/br * Or' ← ∨ And
/br And ← Compare And'
/br * And' ← ∧ Compare
/br Compare ← Sum Compare'
/br * Compare' ← > Sum
/br Sum ← Product Sum'
/br * Sum' ←+Product
/br Product ← Unary Product'
/br * Product' ← * Unary
/br Unary ←-Unary / Id.Unary / {N} Unary / Power
/br Power ← Atom Power'
/br * Power' ← sub Unary
/br Atom ← (E) / [E EL'] / String / Declare Declare' E / if E then E IF else E / Name (E EL') / Name
/br Name ← Id:Type / Id
/br Id ← !, ! [! (!] !) !:!.! dq any
/br comma? ←, /
/br * IF ← else if E then E
/br Type ← Id.Type / Id
/br Declare ← let any = E comma? / assert E report E comma? / {N} comma? / for ForDeclare do E comma? / for ForDeclare while E do E comma?
/br ForDeclare ← AccumList, any ∈ E / AccumList
/br AccumList ← ! while any = E AccumList'
/br * AccumList' ←, any = E
/br * Declare' ← Declare
/br FPL ← FP FPL'
/br * FPL' ←, FP
/br FP ← any:Type / Type
/br * N ← {N} / !} any

function action(partno:int, R:seq.seq.symbol, rinfo:resultType) seq.symbol
if partno = 2 then mergeText(R sub (n.R - 1), R sub n.R)
else if partno = 3 then mergeText(R sub (n.R - 1), R sub n.R)
else if partno = 4 then strExp(R sub n.R, "", true, empty:seq.symbol)
else if partno = 5 then strExp(R sub (n.R - 1), "", true, R sub n.R)
else if partno = 6 then strExp(R sub n.R, [toword.firsttoken.rinfo], false, empty:seq.symbol)
else if partno = 7 then strExp(R sub (n.R - 1), worddata.R sub n.R, false, empty:seq.symbol)
else if partno = 9 then R sub n.R
else if partno = 10 then [Lit(1 + noargs.R sub (n.R - 1))] + R sub (n.R - 1) << 1 + R sub n.R
else if partno = 11 then R sub (n.R - 1) + R sub n.R
else if partno = 12 then binary(R sub (n.R - 1), firsttoken.rinfo, R sub n.R)
else if partno = 13 then R sub (n.R - 1) + R sub n.R
else if partno = 14 then binary(R sub (n.R - 1), firsttoken.rinfo, R sub n.R)
else if partno = 15 then R sub (n.R - 1) + R sub n.R
else if partno = 16 then binary(R sub (n.R - 1), firsttoken.rinfo, R sub n.R)
else if partno = 17 then R sub (n.R - 1) + R sub n.R
else if partno = 18 then binary(R sub (n.R - 1), firsttoken.rinfo, R sub n.R)
else if partno = 19 then R sub (n.R - 1) + R sub n.R
else if partno = 20 then binary(R sub (n.R - 1), firsttoken.rinfo, R sub n.R)
else if partno = 21 then R sub n.R + symbol(internalmod, [toword.firsttoken.rinfo], [typeint], typeint)
else if partno = 22 then R sub n.R + symbol(internalmod, worddata.(R sub (n.R - 1)) sub 1, [typeint], typeint)
else if partno = 23 then
 (if isempty.R sub (n.R - 1) then [Words.""] else R sub (n.R - 1))
  + R sub n.R
  + symbol(internalmod, "{", [seqof.typeword, typeint], typeint)
else if partno = 24 then R sub n.R
else if partno = 25 then R sub (n.R - 1) + R sub n.R
else if partno = 26 then binary(R sub (n.R - 1), firsttoken.rinfo, R sub n.R)
else if partno = 27 then R sub n.R + symbol(internalmod, "(", [typeint], typeint)
else if partno = 28 then R sub (n.R - 1) + R sub n.R << 1 + Sequence(typeint, 1 + noargs.R sub n.R)
else if partno = 29 then R sub n.R
else if partno = 30 then mergeText(mergeText(R sub (n.R - 2), R sub (n.R - 1)), R sub n.R)
else if partno = 31 then
 [Start.typeint]
  + R sub (n.R - 3)
  + Br2(1, 2)
  + R sub (n.R - 2)
  + Exit
  + R sub (n.R - 1)
  + R sub n.R
  + EndBlock
else if partno = 32 then
 R sub (n.R - 1)
  + R sub n.R << 1
  + symbol(
  internalmod
  , [merge.worddata.R sub (n.R - 2)]
  , constantseq(1 + noargs.R sub n.R, typeint)
  , if n.worddata.R sub (n.R - 2) > 1 then compoundNameType else typeint
 )
else if partno = 33 then
 [
  Local(
   merge.worddata.R sub n.R
   , if n.worddata.R sub n.R > 1 then compoundNameType else typeint
   , 0
  )
 ]
else if partno = 34 then R sub (n.R - 1) + Words.":" + R sub n.R
else if partno = 35 then R sub n.R
else if partno = 36 then R sub n.R
else if partno = 37 then R sub n.R
else if partno = 38 then R sub n.R
else if partno = 39 then R sub (n.R - 2) + R sub (n.R - 1) + Br2(1, 2) + R sub n.R + Exit
else if partno = 40 then R sub (n.R - 1) + Words."." + R sub n.R
else if partno = 41 then R sub n.R
else if partno = 42 then R sub (n.R - 1) + Define(name.(R sub (n.R - 2)) sub 1, 1)
else if partno = 43 then
 R sub (n.R - 2)
  + R sub (n.R - 1)
  + symbol(internalmod, "$assert", [typeboolean, seqof.typeword], typeint)
else if partno = 44 then
 R sub (n.R - 2)
  + Words.worddata.R sub (n.R - 1)
  + symbol(internalmod, "{", [seqof.typeword], typeint)
else if partno = 45 then forbody(R sub (n.R - 2), [Littrue], R sub (n.R - 1))
else if partno = 46 then forbody(R sub (n.R - 3), R sub (n.R - 2), R sub (n.R - 1))
else if partno = 47 then forseq(R sub (n.R - 2), R sub (n.R - 1), R sub n.R)
else if partno = 48 then forseq(R sub n.R, [Words."."], [Words."."])
else if partno = 49 then
 [Lit(1 + noargs.R sub n.R)]
  + R sub (n.R - 2)
  + subseq(R sub n.R, 2, 1 + noargs.R sub n.R)
  + R sub (n.R - 1)
  + R sub n.R << (1 + noargs.R sub n.R)
else if partno = 50 then forseq(R sub (n.R - 2), R sub (n.R - 1), R sub n.R)
else if partno = 51 then mergeText(R sub (n.R - 1), R sub n.R)
else if partno = 52 then R sub (n.R - 1)
else if partno = 53 then R sub n.R
else if partno = 54 then empty:seq.symbol
else if partno = 55 then empty:seq.symbol
else R sub 1

function mytable seq.tblEle
[
 {1} tblEle(NT.T'.2, totoken."?" sub 1, Match, Failure, "")
 , {2} tblEle(T', totoken."function" sub 1, NT.3, Fail, "function Name (FPL) Type E")
 , {3} tblEle(NT.88, totoken."Name" sub 1, T'.4, Fail, "Name (FPL) Type E")
 , {4} tblEle(T', totoken."(" sub 1, NT.5, NT.12, "(FPL) Type E")
 , {5} tblEle(NT.153, totoken."FPL" sub 1, T.6, T.10, "FPL) Type E")
 , {6} tblEle(T, totoken.")" sub 1, NT.7, T.10, ") Type E")
 , {7} tblEle(NT.107, totoken."Type" sub 1, NT.8, T.10, "Type E")
 , {8} tblEle(NT.152, totoken."Declare'" sub 1, NT.9, T.10, "E")
 , {9} tblEle(NT.27, totoken."E" sub 1, Reduce.2, T.10, "E")
 , {10} tblEle(T, totoken."function" sub 1, NT.11, Fail, "function Name Type E")
 , {11} tblEle(NT.88, totoken."Name" sub 1, NT.12, Fail, "Name Type E")
 , {12} tblEle(NT.107, totoken."Type" sub 1, NT.13, Fail, "Type E")
 , {13} tblEle(NT.152, totoken."Declare'" sub 1, NT.14, Fail, "E")
 , {14} tblEle(NT.27, totoken."E" sub 1, Reduce.3, Fail, "E")
 , {15} tblEle(T, totoken.dq sub 1, NT.16, Fail, "dq dq")
 , {16} tblEle(NT.T'.18, totoken."String'" sub 1, T.17, Fail, "dq")
 , {17} tblEle(T, totoken.dq sub 1, Reduce.4, Fail, "dq")
 , {18} tblEle(T', totoken.colon sub 1, T.19, NT.23, "colon (E)")
 , {19} tblEle(T, totoken."(" sub 1, NT.20, T'.22, "(E)")
 , {20} tblEle(NT.27, totoken."E" sub 1, T.21, T'.22, "E)")
 , {21} tblEle(T, totoken.")" sub 1, Reduce*(5, T'.18), T'.22, ")")
 , {22} tblEle(T', totoken.colon sub 1, Reduce*(6, T'.18), NT.23, "colon")
 , {23} tblEle(NT.!T.24, totoken."str2" sub 1, Reduce*(7, T'.18), Success*, "str2")
 , {24} tblEle(!T, totoken.dq sub 1, Fail, !T.25, "dq any")
 , {25} tblEle(!T, totoken.colon sub 1, Fail, MatchAny.26, "colon any")
 , {26} tblEle(MatchAny, totoken."?" sub 1, Discard*.!T.166, Fail, "any")
 , {27} tblEle(NT.30, totoken."Or" sub 1, Reduce.9, Fail, "Or")
 , {28} tblEle(T, totoken."," sub 1, NT.29, Success*, ", E")
 , {29} tblEle(NT.27, totoken."E" sub 1, Reduce*(10, T.28), Success*, "E")
 , {30} tblEle(NT.34, totoken."And" sub 1, NT.31, Fail, "And")
 , {31} tblEle(NT.T.32, totoken."Or'" sub 1, Reduce.11, Fail, "")
 , {32} tblEle(T, totoken."∨" sub 1, NT.33, Success*, "∨ And")
 , {33} tblEle(NT.34, totoken."And" sub 1, Reduce*(12, T.32), Success*, "And")
 , {34} tblEle(NT.38, totoken."Compare" sub 1, NT.35, Fail, "Compare")
 , {35} tblEle(NT.T.36, totoken."And'" sub 1, Reduce.13, Fail, "")
 , {36} tblEle(T, totoken."∧" sub 1, NT.37, Success*, "∧ Compare")
 , {37} tblEle(NT.38, totoken."Compare" sub 1, Reduce*(14, T.36), Success*, "Compare")
 , {38} tblEle(NT.42, totoken."Sum" sub 1, NT.39, Fail, "Sum")
 , {39} tblEle(NT.T.40, totoken."Compare'" sub 1, Reduce.15, Fail, "")
 , {40} tblEle(T, totoken.">" sub 1, NT.41, Success*, "> Sum")
 , {41} tblEle(NT.42, totoken."Sum" sub 1, Reduce*(16, T.40), Success*, "Sum")
 , {42} tblEle(NT.46, totoken."Product" sub 1, NT.43, Fail, "Product")
 , {43} tblEle(NT.T.44, totoken."Sum'" sub 1, Reduce.17, Fail, "")
 , {44} tblEle(T, totoken."+" sub 1, NT.45, Success*, "+Product")
 , {45} tblEle(NT.46, totoken."Product" sub 1, Reduce*(18, T.44), Success*, "Product")
 , {46} tblEle(NT.T'.50, totoken."Unary" sub 1, NT.47, Fail, "Unary")
 , {47} tblEle(NT.T.48, totoken."Product'" sub 1, Reduce.19, Fail, "")
 , {48} tblEle(T, totoken."*" sub 1, NT.49, Success*, "* Unary")
 , {49} tblEle(NT.T'.50, totoken."Unary" sub 1, Reduce*(20, T.48), Success*, "Unary")
 , {50} tblEle(T', totoken."-" sub 1, NT.51, NT.52, "-Unary")
 , {51} tblEle(NT.T'.50, totoken."Unary" sub 1, Reduce.21, NT.52, "Unary")
 , {52} tblEle(NT.!T.92, totoken."Id" sub 1, T.53, T'.55, "Id.Unary")
 , {53} tblEle(T, totoken."." sub 1, NT.54, T'.55, ".Unary")
 , {54} tblEle(NT.T'.50, totoken."Unary" sub 1, Reduce.22, T'.55, "Unary")
 , {55} tblEle(T', totoken."{" sub 1, NT.56, NT.59, "{} Unary")
 , {56} tblEle(NT.T.161, totoken."N" sub 1, T.57, NT.59, "} Unary")
 , {57} tblEle(T, totoken."}" sub 1, NT.58, NT.59, "} Unary")
 , {58} tblEle(NT.T'.50, totoken."Unary" sub 1, Reduce.23, NT.59, "Unary")
 , {59} tblEle(NT.60, totoken."Power" sub 1, Reduce.24, Fail, "Power")
 , {60} tblEle(NT.T'.64, totoken."Atom" sub 1, NT.61, Fail, "Atom")
 , {61} tblEle(NT.T.62, totoken."Power'" sub 1, Reduce.25, Fail, "")
 , {62} tblEle(T, totoken."sub" sub 1, NT.63, Success*, "sub Unary")
 , {63} tblEle(NT.T'.50, totoken."Unary" sub 1, Reduce*(26, T.62), Success*, "Unary")
 , {64} tblEle(T', totoken."(" sub 1, NT.65, T'.67, "(E)")
 , {65} tblEle(NT.27, totoken."E" sub 1, T.66, T'.67, "E)")
 , {66} tblEle(T, totoken.")" sub 1, Reduce.27, T'.67, ")")
 , {67} tblEle(T', totoken."[" sub 1, NT.68, NT.71, "[E]")
 , {68} tblEle(NT.27, totoken."E" sub 1, NT.69, NT.71, "E]")
 , {69} tblEle(NT.T.28, totoken."EL'" sub 1, T.70, NT.71, "]")
 , {70} tblEle(T, totoken."]" sub 1, Reduce.28, NT.71, "]")
 , {71} tblEle(NT.T.15, totoken."String" sub 1, Reduce.29, NT.72, "String")
 , {72} tblEle(NT.T'.111, totoken."Declare" sub 1, NT.73, T'.75, "Declare E")
 , {73} tblEle(NT.152, totoken."Declare'" sub 1, NT.74, T'.75, "E")
 , {74} tblEle(NT.27, totoken."E" sub 1, Reduce.30, T'.75, "E")
 , {75} tblEle(T', totoken."if" sub 1, NT.76, NT.82, "if E then E else E")
 , {76} tblEle(NT.27, totoken."E" sub 1, T.77, NT.82, "E then E else E")
 , {77} tblEle(T, totoken."then" sub 1, NT.78, NT.82, "then E else E")
 , {78} tblEle(NT.27, totoken."E" sub 1, NT.79, NT.82, "E else E")
 , {79} tblEle(NT.T.102, totoken."IF" sub 1, T.80, NT.82, "else E")
 , {80} tblEle(T, totoken."else" sub 1, NT.81, NT.82, "else E")
 , {81} tblEle(NT.27, totoken."E" sub 1, Reduce.31, NT.82, "E")
 , {82} tblEle(NT.88, totoken."Name" sub 1, T.83, Fail, "Name (E)")
 , {83} tblEle(T, totoken."(" sub 1, NT.84, NT.87, "(E)")
 , {84} tblEle(NT.27, totoken."E" sub 1, NT.85, NT.87, "E)")
 , {85} tblEle(NT.T.28, totoken."EL'" sub 1, T.86, NT.87, ")")
 , {86} tblEle(T, totoken.")" sub 1, Reduce.32, NT.87, ")")
 , {87} tblEle(NT.88, totoken."Name" sub 1, Reduce.33, Fail, "Name")
 , {88} tblEle(NT.!T.92, totoken."Id" sub 1, T.89, Fail, "Id:Type")
 , {89} tblEle(T, totoken.":" sub 1, NT.90, NT.91, ":Type")
 , {90} tblEle(NT.107, totoken."Type" sub 1, Reduce.34, NT.91, "Type")
 , {91} tblEle(NT.!T.92, totoken."Id" sub 1, Reduce.35, Fail, "Id")
 , {92} tblEle(!T, totoken."," sub 1, Fail, !T.93, ", any")
 , {93} tblEle(!T, totoken."[" sub 1, Fail, !T.94, "[any")
 , {94} tblEle(!T, totoken."(" sub 1, Fail, !T.95, "(any")
 , {95} tblEle(!T, totoken."]" sub 1, Fail, !T.96, "] any")
 , {96} tblEle(!T, totoken.")" sub 1, Fail, !T.97, ") any")
 , {97} tblEle(!T, totoken.":" sub 1, Fail, !T.98, ":any")
 , {98} tblEle(!T, totoken."." sub 1, Fail, !T.99, ".any")
 , {99} tblEle(!T, totoken.dq sub 1, Fail, MatchAny.100, "dq any")
 , {100} tblEle(MatchAny, totoken."?" sub 1, Reduce.36, Fail, "any")
 , {101} tblEle(T, totoken."," sub 1, Reduce.37, Reduce.38, ",")
 , {102} tblEle(T, totoken."else" sub 1, T.103, Success*, "else if E then E")
 , {103} tblEle(T, totoken."if" sub 1, NT.104, Success*, "if E then E")
 , {104} tblEle(NT.27, totoken."E" sub 1, T.105, Success*, "E then E")
 , {105} tblEle(T, totoken."then" sub 1, NT.106, Success*, "then E")
 , {106} tblEle(NT.27, totoken."E" sub 1, Reduce*(39, T.102), Success*, "E")
 , {107} tblEle(NT.!T.92, totoken."Id" sub 1, T.108, Fail, "Id.Type")
 , {108} tblEle(T, totoken."." sub 1, NT.109, NT.110, ".Type")
 , {109} tblEle(NT.107, totoken."Type" sub 1, Reduce.40, NT.110, "Type")
 , {110} tblEle(NT.!T.92, totoken."Id" sub 1, Reduce.41, Fail, "Id")
 , {111} tblEle(T', totoken."let" sub 1, MatchAny.112, T'.116, "let any = E")
 , {112} tblEle(MatchAny, totoken."?" sub 1, T.113, T'.116, "any = E")
 , {113} tblEle(T, totoken."=" sub 1, NT.114, T'.116, "= E")
 , {114} tblEle(NT.27, totoken."E" sub 1, NT.115, T'.116, "E")
 , {115} tblEle(NT.T.101, totoken."comma?" sub 1, Reduce.42, T'.116, "")
 , {116} tblEle(T', totoken."assert" sub 1, NT.117, T'.121, "assert E report E")
 , {117} tblEle(NT.27, totoken."E" sub 1, T.118, T'.121, "E report E")
 , {118} tblEle(T, totoken."report" sub 1, NT.119, T'.121, "report E")
 , {119} tblEle(NT.27, totoken."E" sub 1, NT.120, T'.121, "E")
 , {120} tblEle(NT.T.101, totoken."comma?" sub 1, Reduce.43, T'.121, "")
 , {121} tblEle(T', totoken."{" sub 1, NT.122, T'.125, "{}")
 , {122} tblEle(NT.T.161, totoken."N" sub 1, T.123, T'.125, "}")
 , {123} tblEle(T, totoken."}" sub 1, NT.124, T'.125, "}")
 , {124} tblEle(NT.T.101, totoken."comma?" sub 1, Reduce.44, T'.125, "")
 , {125} tblEle(T', totoken."for" sub 1, NT.126, Fail, "for ForDeclare do E")
 , {126} tblEle(NT.137, totoken."ForDeclare" sub 1, T'.127, Fail, "ForDeclare do E")
 , {127} tblEle(T', totoken."do" sub 1, NT.128, T.132, "do E")
 , {128} tblEle(NT.27, totoken."E" sub 1, NT.129, T.130, "E")
 , {129} tblEle(NT.T.101, totoken."comma?" sub 1, Reduce.45, T.130, "")
 , {130} tblEle(T, totoken."for" sub 1, NT.131, Fail, "for ForDeclare while E do E")
 , {131} tblEle(NT.137, totoken."ForDeclare" sub 1, T.132, Fail, "ForDeclare while E do E")
 , {132} tblEle(T, totoken."while" sub 1, NT.133, Fail, "while E do E")
 , {133} tblEle(NT.27, totoken."E" sub 1, T.134, Fail, "E do E")
 , {134} tblEle(T, totoken."do" sub 1, NT.135, Fail, "do E")
 , {135} tblEle(NT.27, totoken."E" sub 1, NT.136, Fail, "E")
 , {136} tblEle(NT.T.101, totoken."comma?" sub 1, Reduce.46, Fail, "")
 , {137} tblEle(NT.!T.143, totoken."AccumList" sub 1, T.138, Fail, "AccumList, any ∈ E")
 , {138} tblEle(T, totoken."," sub 1, MatchAny.139, NT.142, ", any ∈ E")
 , {139} tblEle(MatchAny, totoken."?" sub 1, T.140, NT.142, "any ∈ E")
 , {140} tblEle(T, totoken."∈" sub 1, NT.141, NT.142, "∈ E")
 , {141} tblEle(NT.27, totoken."E" sub 1, Reduce.47, NT.142, "E")
 , {142} tblEle(NT.!T.143, totoken."AccumList" sub 1, Reduce.48, Fail, "AccumList")
 , {143} tblEle(!T, totoken."while" sub 1, Fail, MatchAny.144, "while any = E")
 , {144} tblEle(MatchAny, totoken."?" sub 1, T.145, Fail, "any = E")
 , {145} tblEle(T, totoken."=" sub 1, NT.146, Fail, "= E")
 , {146} tblEle(NT.27, totoken."E" sub 1, NT.147, Fail, "E")
 , {147} tblEle(NT.T.148, totoken."AccumList'" sub 1, Reduce.49, Fail, "")
 , {148} tblEle(T, totoken."," sub 1, MatchAny.149, Success*, ", any = E")
 , {149} tblEle(MatchAny, totoken."?" sub 1, T.150, Success*, "any = E")
 , {150} tblEle(T, totoken."=" sub 1, NT.151, Success*, "= E")
 , {151} tblEle(NT.27, totoken."E" sub 1, Reduce*(50, T.148), Success*, "E")
 , {152}
 tblEle(NT.T'.111, totoken."Declare" sub 1, Reduce*(51, NT.152), Success*, "Declare")
 , {153} tblEle(NT.MatchAny.157, totoken."FP" sub 1, NT.154, Fail, "FP")
 , {154} tblEle(NT.T.155, totoken."FPL'" sub 1, Reduce.52, Fail, "")
 , {155} tblEle(T, totoken."," sub 1, NT.156, Success*, ", FP")
 , {156} tblEle(NT.MatchAny.157, totoken."FP" sub 1, Reduce*(53, T.155), Success*, "FP")
 , {157} tblEle(MatchAny, totoken."?" sub 1, T.158, NT.160, "any:Type")
 , {158} tblEle(T, totoken.":" sub 1, NT.159, NT.160, ":Type")
 , {159} tblEle(NT.107, totoken."Type" sub 1, Reduce.54, NT.160, "Type")
 , {160} tblEle(NT.107, totoken."Type" sub 1, Reduce.55, Fail, "Type")
 , {161} tblEle(T, totoken."{" sub 1, NT.162, !T.164, "{}")
 , {162} tblEle(NT.T.161, totoken."N" sub 1, T.163, !T.164, "}")
 , {163} tblEle(T, totoken."}" sub 1, Discard*.T.161, !T.164, "}")
 , {164} tblEle(!T, totoken."}" sub 1, All, MatchAny.165, "} any")
 , {165} tblEle(MatchAny, totoken."?" sub 1, Discard*.T.161, All, "any")
 , {166} tblEle(!T, totoken.dq sub 1, All, !T.167, "dq any")
 , {167} tblEle(!T, totoken.colon sub 1, All, MatchAny.168, "colon any")
 , {168} tblEle(MatchAny, totoken."?" sub 1, Discard*.!T.166, All, "any")
]

function =(seq.word, seq.symbol) boolean true

function $(int) seq.symbol empty:seq.seq.symbol sub 1

use standard

use seq.tblEle

use seq1.frame

use stack.frame

use seq1.seq.symbol

use PEGrules

type tblEle is action:state, match:token, Sstate:state, Fstate:state, recover:seq.word

function recoveryEnding(rinfo:resultType) seq.word
for acc = "", frame ∈ reverse.toseq.stk.rinfo
do
 if action.Sstate.frame ∈ [T, T', NT] then acc + recover.mytable sub index.Sstate.frame
 else acc,
acc

type frame is
Sstate:state
, Fstate:state
, i:int
, result:seq.seq.symbol
, faili:int
, failresult:seq.seq.symbol

type resultType is stk:stack.frame, input:seq.token, place:int, faili:int

Function status(a:resultType) word
if Sstate.top.stk.a ≠ Match then 'Failed
else if place.a = {length of input} faili.top.stk.a then 'Match
else 'MatchPrefix

Function result(a:resultType) seq.symbol
let t = result.top.stk.a,
t sub n.t

function parse(myinput0:seq.token, initAttr:seq.symbol) resultType
let myinput = packed(myinput0 + endMark)
let packedTable = packed.mytable
for
 rinfo = resultType(empty:stack.frame, myinput, 0, 1)
 , stk = empty:stack.frame
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
    rinfo
    , pop.stk
    , nextState.Fstate.top
    , newi
    , idxNB(myinput, newi)
    , result.top
    , faili.top
    , failresult.top
   )
  else
   next(
    rinfo
    , pop.stk
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
  next(rinfo, pop.stk, Sstate.top, i, inputi, result.top + result, faili.top, failresult.top)
 else if actionState = Discard* then
  let top = top.stk
  let newrinfo = if i > place.rinfo then resultType(stk, myinput, i, faili) else rinfo,
  next(newrinfo, stk, nextState.state, i, inputi, result.top, i, result.top)
 else if actionState = All then
  let top = top.stk
  let att = [toAttribute(result sub n.result, subseq(myinput, i.top, i - 1))],
  next(rinfo, pop.stk, Sstate.top, i, inputi, result.top + att, faili.top, failresult.top)
 else if actionState = Lambda then
  let newrinfo = if i > place.rinfo then resultType(stk, myinput, i, faili) else rinfo
  let att = [action(reduceNo.state, result, newrinfo)],
  next(newrinfo, stk, nextState2.state, i, inputi, result + att, faili, failresult)
 else if actionState = Reduce then
  let top = top.stk
  let newrinfo =
   if i > place.rinfo ∨ faili ≠ faili.rinfo then resultType(stk, myinput, i, faili)
   else rinfo,
  let att = [action(reduceNo.state, result, newrinfo)],
  next(newrinfo, pop.stk, Sstate.top, i, inputi, result.top + att, faili.top, failresult.top)
 else if actionState = Reduce* then
  let newrinfo =
   if i > place.rinfo ∨ faili ≠ faili.rinfo then resultType(stk, myinput, i, faili)
   else rinfo
  let att = [action(reduceNo.state, result, newrinfo)],
  let top = top.stk,
  next(newrinfo, stk, nextState.state, i, inputi, att, i, att)
 else if actionState = !Reduce then
  let top = top.stk
  let ini = idxNB(myinput, faili.top),
  next(rinfo, pop.stk, Fstate.top, faili.top, ini, failresult.top, faili.top, failresult.top)
 else if actionState = !Fail then
  let top = top.stk
  let ini = idxNB(myinput, i.top),
  next(rinfo, pop.stk, Sstate.top, i.top, ini, result.top, faili.top, failresult.top)
 else if actionState = T then
  let te = idxNB(packedTable, index.state),
  if inputi ≠ match.te then
   {fail}
   next(rinfo, stk, Fstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)
  else next(rinfo, stk, Sstate.te, i + 1, idxNB(myinput, i + 1), result, faili, failresult)
 else if actionState = !T then
  let te = idxNB(packedTable, index.state),
  if inputi = match.te then
   {fail}
   next(rinfo, stk, Sstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)
  else next(rinfo, stk, Fstate.te, i, inputi, result, faili, failresult)
 else if actionState = MatchAny then
  let te = idxNB(packedTable, index.state),
  if inputi = endMark then {fail} next(rinfo, stk, Fstate.te, i, inputi, result, faili, failresult)
  else
   let reslt = result + toAttribute(result sub n.result, [inputi])
   let ini = idxNB(myinput, i + 1),
   next(rinfo, stk, Sstate.te, i + 1, ini, reslt, faili, failresult)
 else if actionState = T' then
  let te = idxNB(packedTable, index.state),
  if inputi = match.te then next(rinfo, stk, Sstate.te, i + 1, idxNB(myinput, i + 1), result, faili, failresult)
  else next(rinfo, stk, Fstate.te, i, inputi, result, faili, failresult)
 else
  {match non Terminal}
  let te = idxNB(packedTable, index.state)
  assert action.action.te ∈ [NT, NT*] report "PROBLEM PEG:(state)"
  let newstk = push(stk, frame(Sstate.te, Fstate.te, i, result, faili, failresult)),
  let tmp = [toAttribute(result sub n.result, empty:seq.token)],
  next(rinfo, newstk, nextState.action.te, i, inputi, tmp, i, tmp),
resultType(
 push(stk.rinfo, frame(state, state, place.rinfo, result, n.myinput, result))
 , input.rinfo
 , place.rinfo
 , faili.rinfo
) 
