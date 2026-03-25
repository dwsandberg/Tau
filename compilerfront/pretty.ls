Module pretty

use UTF8

use autolink

use set.autolink

use file

use seq.file

use seq.filename

use format1a

use stack.int

use seq1.mytype

use prettyR

use standard

use seq.symbol

use set.symbol

use symbol1

use token

use seq.token

use seq.word

use seq.seq.word

use set.seq.word

use sort.seq.word

use seq1.word

use sort.word

Export id(symbol) seq.word {From prettyR}

Export type:autolink{From prettyR}

Export file(autolink) seq.word {From prettyR}

Export id(autolink) seq.word {From prettyR}

Export autolink(seq.word, seq.word) autolink {From prettyR}

Export >1(a:autolink, b:autolink) ordering {From prettyR}

Export >2(a:autolink, b:autolink) ordering {From prettyR}

Export prettyX(
srctxt:seq.word
, code:seq.symbol
, syms:set.autolink
, change:boolean
, totxt:boolean
) seq.word

Export removeMarkup(s:seq.word) seq.word

Export showZ(seq.word) seq.word {From prettySupport}

Function sortuse(b:seq.seq.word, prefix:seq.word) seq.seq.word
for a = empty:seq.seq.word, u ∈ b do a + reverse.u
for acc = empty:seq.seq.word, @e ∈ sort>alpha.toseq.asset.a do acc + (prefix + reverse.@e),
acc

Function pretty(p:seq.word) seq.word pretty(p, true)

Function libsrc(m:midpoint, outfn:seq.filename) seq.file
let outname = outfn sub 1
for only = "", full = false, fn ∈ outfn
do
 if ext.fn ∈ "libsrc" then if name.outname = name.fn then next(only, true) else next(only + name.fn, full)
 else next(only, full)
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
    else
     libs
     + file(filename("+:(dirpath.outname)" + libname + ".libsrc"), toseqbyte.textFormat.libtxt),
   next(newlibname, all + "/p" + libtxt, p, newlibs)
 else next(libname, all, libtxt + "/p" + pretty(p, false, true), libs),
if full then [file(changeext(outname, "libsrc"), toseqbyte.textFormat.all)] + libs
else libs

Function pretty(p:seq.word, change:boolean) seq.word pretty(p, change, false)

Function pretty(p:seq.word, change:boolean, totxt:boolean) seq.word
if p sub 1 ∈ "Function function" then
 assert opprec."+" sub 1 = 4 report "no prec specified"
 let r = parse(totokens.p, empty:seq.symbol),
 if status.r ∈ "Match MatchPrefix" then prettyX(p, result.r, empty:set.autolink, change, totxt)
 else [status.r] + %.result.r
else prettyX(p, empty:seq.symbol, empty:set.autolink, change, totxt)

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

function strExp(code:seq.symbol, str:seq.word, expcode:seq.symbol) seq.symbol
{assert not.isempty.str report"code:(code)expcode:(expcode)"}
if isempty.str ∧ isempty.code then [Words.""] + expcode + catStringOp
else
 let code0 =
  if not.isempty.code ∧ kind.last.code = kwords then if isempty.str then code else [Words(worddata.last.code + str)]
  else if isempty.str then code
  else if isempty.code then [Words.str]
  else code + Words.str + catStringOp,
 if isempty.expcode then code0
 else if isempty.code0 then expcode
 else code0 + expcode + catStringOp

function catStringOp symbol
symbol(moduleref("* seq", typeword), "+", [seqof.typeword, seqof.typeword], seqof.typeword)

function mergeText(a:seq.symbol, b:seq.symbol) seq.symbol
if not.isempty.a ∧ not.isempty.b then a + b + symbol(internalmod, "$mergecode", [typeint, typeint], typeint)
else a + b

Function forbody(vars:seq.symbol, exitexp:seq.symbol, forbody:seq.symbol) seq.symbol
let n = value.vars sub 1
let textvars = subseq(vars, 2, n + 1)
let codevars =
 vars << (n + 1) >> (if worddata.vars sub n.vars = "." then 1 else 0)
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
{wordmap: colon totoken.colon sub 1, dq totoken.dq sub 1, totoken."$"sub 1}
[
 "Parser function Name(FPL)Type Declare' E" = mergeText($.4, $.5)
 , "/ function Name Type Declare' E" = mergeText($.3, $.4)
 , "String dq dq" = [Words.""]
 , "/ dq String' dq" = $.1
 , "* String' colon(E)" = strExp($.0, "", $.1)
 , "/ colon" = strExp($.0, ":", empty:seq.symbol)
 , "/ str2" = strExp($.0, worddata.$.1, empty:seq.symbol)
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
 , "/{N}Unary"
 = (if isempty.$.1 then [Words.""] else $.1)
 + $.2
 + symbol(internalmod, "{", [seqof.typeword, typeint], typeint)
 , "/ Power" = $.1
 , "Power Atom Power'" = $.1 + $.2
 , "* Power' sub Unary" = binary($.0, firsttoken.rinfo, $.1)
 , "Atom(E)" = $.1 + symbol(internalmod, "(", [typeint], typeint)
 , "/[E EL']" = $.1 + $.2 << 1 + Sequence(typeint, 1 + noargs.$.2)
 , "/ String" = $.1
 , "/ Declare Declare' E" = mergeText(mergeText($.1, $.2), $.3)
 , "/ if E then E IF else E"
 = [Start.typeint] + $.1 + Br2(1, 2) + $.2 + Exit + $.3 + $.4 + EndBlock
 , "/ Name(E EL')"
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
 , "Id !, ![!(!]!)!:!.! dq any" = $.1
 , "comma?," = $.0
 , "/" = $.0
 , "* IF else if E then E" = $.0 + $.1 + Br2(1, 2) + $.2 + Exit
 , "Type Id.Type" = $.1 + Words."." + $.2
 , "/ Id" = $.1
 , "Declare let any = E comma?" = $.2 + Define(name.($.1) sub 1, 1)
 , "/ assert E report E comma?"
 = $.1 + $.2 + symbol(internalmod, "$assert", [typeboolean, seqof.typeword], typeint)
 , "/{N}comma?"
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
 , "* N{N}" = /All
 , "/ !}any" = /All
]

<<<< Below is auto generated code >>>>

/br Non-terminals:AccumList AccumList' And And' Atom Compare Compare' Declare Declare' E EL' FP FPL FPL' ForDeclare IF Id N Name Or Or' Parser Power Power' Product Product' String String' Sum Sum' Type Unary comma? str2 /br
Terminals:()*+,-.:= >[]any assert colon do dq else for function if let report sub then while{}∈ ∧ ∨ /br
Parser ← function Name(FPL)Type Declare' E / function Name Type Declare' E /br
String ← dq dq / dq String' dq /br
* String' ← colon(E)/ colon / str2 /br
+str2 ← ! dq ! colon any /br
E ← Or /br
* EL' ←, E /br
Or ← And Or' /br
* Or' ← ∨ And /br
And ← Compare And' /br
* And' ← ∧ Compare /br
Compare ← Sum Compare' /br
* Compare' ← > Sum /br
Sum ← Product Sum' /br
* Sum' ←+Product /br
Product ← Unary Product' /br
* Product' ← * Unary /br
Unary ←-Unary / Id.Unary /{N}Unary / Power /br
Power ← Atom Power' /br
* Power' ← sub Unary /br
Atom ←(E)/[E EL']/ String / Declare Declare' E / if E then E IF else E / Name(E EL')/ Name /br
Name ← Id:Type / Id /br
Id ← !, ![!(!]!)!:!.! dq any /br
comma? ←, / /br
* IF ← else if E then E /br
Type ← Id.Type / Id /br
Declare ← let any = E comma? / assert E report E comma? /{N}comma? / for ForDeclare do E comma? / for ForDeclare while E do E comma? /br
ForDeclare ← AccumList, any ∈ E / AccumList /br
AccumList ← ! while any = E AccumList' /br
* AccumList' ←, any = E /br
* Declare' ← Declare /br
FPL ← FP FPL' /br
* FPL' ←, FP /br
FP ← any:Type / Type /br
* N ←{N}/ !}any

function action(partno:int, R:seq.seq.symbol, rinfo:resultType) seq.symbol
if partno = 2 then mergeText(R sub (n.R - 1), R sub n.R)
else if partno = 3 then mergeText(R sub (n.R - 1), R sub n.R)
else if partno = 4 then [Words.""]
else if partno = 5 then R sub n.R
else if partno = 6 then strExp(R sub (n.R - 1), "", R sub n.R)
else if partno = 7 then strExp(R sub n.R, ":", empty:seq.symbol)
else if partno = 8 then strExp(R sub (n.R - 1), worddata.R sub n.R, empty:seq.symbol)
else if partno = 10 then R sub n.R
else if partno = 11 then [Lit(1 + noargs.R sub (n.R - 1))] + R sub (n.R - 1) << 1 + R sub n.R
else if partno = 12 then R sub (n.R - 1) + R sub n.R
else if partno = 13 then binary(R sub (n.R - 1), firsttoken.rinfo, R sub n.R)
else if partno = 14 then R sub (n.R - 1) + R sub n.R
else if partno = 15 then binary(R sub (n.R - 1), firsttoken.rinfo, R sub n.R)
else if partno = 16 then R sub (n.R - 1) + R sub n.R
else if partno = 17 then binary(R sub (n.R - 1), firsttoken.rinfo, R sub n.R)
else if partno = 18 then R sub (n.R - 1) + R sub n.R
else if partno = 19 then binary(R sub (n.R - 1), firsttoken.rinfo, R sub n.R)
else if partno = 20 then R sub (n.R - 1) + R sub n.R
else if partno = 21 then binary(R sub (n.R - 1), firsttoken.rinfo, R sub n.R)
else if partno = 22 then R sub n.R + symbol(internalmod, [toword.firsttoken.rinfo], [typeint], typeint)
else if partno = 23 then R sub n.R + symbol(internalmod, worddata.(R sub (n.R - 1)) sub 1, [typeint], typeint)
else if partno = 24 then
 (if isempty.R sub (n.R - 1) then [Words.""] else R sub (n.R - 1))
 + R sub n.R
 + symbol(internalmod, "{", [seqof.typeword, typeint], typeint)
else if partno = 25 then R sub n.R
else if partno = 26 then R sub (n.R - 1) + R sub n.R
else if partno = 27 then binary(R sub (n.R - 1), firsttoken.rinfo, R sub n.R)
else if partno = 28 then R sub n.R + symbol(internalmod, "(", [typeint], typeint)
else if partno = 29 then R sub (n.R - 1) + R sub n.R << 1 + Sequence(typeint, 1 + noargs.R sub n.R)
else if partno = 30 then R sub n.R
else if partno = 31 then mergeText(mergeText(R sub (n.R - 2), R sub (n.R - 1)), R sub n.R)
else if partno = 32 then
 [Start.typeint]
 + R sub (n.R - 3)
 + Br2(1, 2)
 + R sub (n.R - 2)
 + Exit
 + R sub (n.R - 1)
 + R sub n.R
 + EndBlock
else if partno = 33 then
 R sub (n.R - 1)
 + R sub n.R << 1
 + symbol(
  internalmod
  , [merge.worddata.R sub (n.R - 2)]
  , constantseq(1 + noargs.R sub n.R, typeint)
  , if n.worddata.R sub (n.R - 2) > 1 then compoundNameType else typeint
 )
else if partno = 34 then
 [
  Local(
   merge.worddata.R sub n.R
   , if n.worddata.R sub n.R > 1 then compoundNameType else typeint
   , 0
  )
 ]
else if partno = 35 then R sub (n.R - 1) + Words.":" + R sub n.R
else if partno = 36 then R sub n.R
else if partno = 37 then R sub n.R
else if partno = 38 then R sub n.R
else if partno = 39 then R sub n.R
else if partno = 40 then R sub (n.R - 2) + R sub (n.R - 1) + Br2(1, 2) + R sub n.R + Exit
else if partno = 41 then R sub (n.R - 1) + Words."." + R sub n.R
else if partno = 42 then R sub n.R
else if partno = 43 then R sub (n.R - 1) + Define(name.(R sub (n.R - 2)) sub 1, 1)
else if partno = 44 then
 R sub (n.R - 2)
 + R sub (n.R - 1)
 + symbol(internalmod, "$assert", [typeboolean, seqof.typeword], typeint)
else if partno = 45 then
 R sub (n.R - 2)
 + Words.worddata.R sub (n.R - 1)
 + symbol(internalmod, "{", [seqof.typeword], typeint)
else if partno = 46 then forbody(R sub (n.R - 2), [Littrue], R sub (n.R - 1))
else if partno = 47 then forbody(R sub (n.R - 3), R sub (n.R - 2), R sub (n.R - 1))
else if partno = 48 then forseq(R sub (n.R - 2), R sub (n.R - 1), R sub n.R)
else if partno = 49 then forseq(R sub n.R, [Words."."], [Words."."])
else if partno = 50 then
 [Lit(1 + noargs.R sub n.R)]
 + R sub (n.R - 2)
 + subseq(R sub n.R, 2, 1 + noargs.R sub n.R)
 + R sub (n.R - 1)
 + R sub n.R << (1 + noargs.R sub n.R)
else if partno = 51 then forseq(R sub (n.R - 2), R sub (n.R - 1), R sub n.R)
else if partno = 52 then mergeText(R sub (n.R - 1), R sub n.R)
else if partno = 53 then R sub (n.R - 1)
else if partno = 54 then R sub n.R
else if partno = 55 then empty:seq.symbol
else if partno = 56 then empty:seq.symbol
else R sub 1

function mytable seq.tblEle
[
 {1}tblEle(NT.T'.2, totoken."?" sub 1, Match, Failure, "")
 , {2}tblEle(T', totoken."function" sub 1, NT.3, Fail, "function Name(FPL)Type E")
 , {3}tblEle(NT.90, totoken."Name" sub 1, T'.4, Fail, "Name(FPL)Type E")
 , {4}tblEle(T', totoken."(" sub 1, NT.5, NT.12, "(FPL)Type E")
 , {5}tblEle(NT.155, totoken."FPL" sub 1, T.6, T.10, "FPL)Type E")
 , {6}tblEle(T, totoken.")" sub 1, NT.7, T.10, ")Type E")
 , {7}tblEle(NT.109, totoken."Type" sub 1, NT.8, T.10, "Type E")
 , {8}tblEle(NT.154, totoken."Declare'" sub 1, NT.9, T.10, "E")
 , {9}tblEle(NT.29, totoken."E" sub 1, Reduce.2, T.10, "E")
 , {10}tblEle(T, totoken."function" sub 1, NT.11, Fail, "function Name Type E")
 , {11}tblEle(NT.90, totoken."Name" sub 1, NT.12, Fail, "Name Type E")
 , {12}tblEle(NT.109, totoken."Type" sub 1, NT.13, Fail, "Type E")
 , {13}tblEle(NT.154, totoken."Declare'" sub 1, NT.14, Fail, "E")
 , {14}tblEle(NT.29, totoken."E" sub 1, Reduce.3, Fail, "E")
 , {15}tblEle(T', totoken.dq sub 1, T'.16, Fail, "dq dq")
 , {16}tblEle(T', totoken.dq sub 1, Reduce.4, NT.18, "dq")
 , {17}tblEle(T, totoken.dq sub 1, NT.18, Fail, "dq dq")
 , {18}tblEle(NT.T'.20, totoken."String'" sub 1, T.19, Fail, "dq")
 , {19}tblEle(T, totoken.dq sub 1, Reduce.5, Fail, "dq")
 , {20}tblEle(T', totoken.colon sub 1, T.21, NT.25, "colon(E)")
 , {21}tblEle(T, totoken."(" sub 1, NT.22, T'.24, "(E)")
 , {22}tblEle(NT.29, totoken."E" sub 1, T.23, T'.24, "E)")
 , {23}tblEle(T, totoken.")" sub 1, Reduce*(6, T'.20), T'.24, ")")
 , {24}tblEle(T', totoken.colon sub 1, Reduce*(7, T'.20), NT.25, "colon")
 , {25}tblEle(NT.!T.26, totoken."str2" sub 1, Reduce*(8, T'.20), Success*, "str2")
 , {26}tblEle(!T, totoken.dq sub 1, Fail, !T.27, "dq any")
 , {27}tblEle(!T, totoken.colon sub 1, Fail, MatchAny.28, "colon any")
 , {28}tblEle(MatchAny, totoken."?" sub 1, Discard*.!T.168, Fail, "any")
 , {29}tblEle(NT.32, totoken."Or" sub 1, Reduce.10, Fail, "Or")
 , {30}tblEle(T, totoken."," sub 1, NT.31, Success*, ", E")
 , {31}tblEle(NT.29, totoken."E" sub 1, Reduce*(11, T.30), Success*, "E")
 , {32}tblEle(NT.36, totoken."And" sub 1, NT.33, Fail, "And")
 , {33}tblEle(NT.T.34, totoken."Or'" sub 1, Reduce.12, Fail, "")
 , {34}tblEle(T, totoken."∨" sub 1, NT.35, Success*, "∨ And")
 , {35}tblEle(NT.36, totoken."And" sub 1, Reduce*(13, T.34), Success*, "And")
 , {36}tblEle(NT.40, totoken."Compare" sub 1, NT.37, Fail, "Compare")
 , {37}tblEle(NT.T.38, totoken."And'" sub 1, Reduce.14, Fail, "")
 , {38}tblEle(T, totoken."∧" sub 1, NT.39, Success*, "∧ Compare")
 , {39}tblEle(NT.40, totoken."Compare" sub 1, Reduce*(15, T.38), Success*, "Compare")
 , {40}tblEle(NT.44, totoken."Sum" sub 1, NT.41, Fail, "Sum")
 , {41}tblEle(NT.T.42, totoken."Compare'" sub 1, Reduce.16, Fail, "")
 , {42}tblEle(T, totoken.">" sub 1, NT.43, Success*, "> Sum")
 , {43}tblEle(NT.44, totoken."Sum" sub 1, Reduce*(17, T.42), Success*, "Sum")
 , {44}tblEle(NT.48, totoken."Product" sub 1, NT.45, Fail, "Product")
 , {45}tblEle(NT.T.46, totoken."Sum'" sub 1, Reduce.18, Fail, "")
 , {46}tblEle(T, totoken."+" sub 1, NT.47, Success*, "+Product")
 , {47}tblEle(NT.48, totoken."Product" sub 1, Reduce*(19, T.46), Success*, "Product")
 , {48}tblEle(NT.T'.52, totoken."Unary" sub 1, NT.49, Fail, "Unary")
 , {49}tblEle(NT.T.50, totoken."Product'" sub 1, Reduce.20, Fail, "")
 , {50}tblEle(T, totoken."*" sub 1, NT.51, Success*, "* Unary")
 , {51}tblEle(NT.T'.52, totoken."Unary" sub 1, Reduce*(21, T.50), Success*, "Unary")
 , {52}tblEle(T', totoken."-" sub 1, NT.53, NT.54, "-Unary")
 , {53}tblEle(NT.T'.52, totoken."Unary" sub 1, Reduce.22, NT.54, "Unary")
 , {54}tblEle(NT.!T.94, totoken."Id" sub 1, T.55, T'.57, "Id.Unary")
 , {55}tblEle(T, totoken."." sub 1, NT.56, T'.57, ".Unary")
 , {56}tblEle(NT.T'.52, totoken."Unary" sub 1, Reduce.23, T'.57, "Unary")
 , {57}tblEle(T', totoken."{" sub 1, NT.58, NT.61, "{}Unary")
 , {58}tblEle(NT.T.163, totoken."N" sub 1, T.59, NT.61, "}Unary")
 , {59}tblEle(T, totoken."}" sub 1, NT.60, NT.61, "}Unary")
 , {60}tblEle(NT.T'.52, totoken."Unary" sub 1, Reduce.24, NT.61, "Unary")
 , {61}tblEle(NT.62, totoken."Power" sub 1, Reduce.25, Fail, "Power")
 , {62}tblEle(NT.T'.66, totoken."Atom" sub 1, NT.63, Fail, "Atom")
 , {63}tblEle(NT.T.64, totoken."Power'" sub 1, Reduce.26, Fail, "")
 , {64}tblEle(T, totoken."sub" sub 1, NT.65, Success*, "sub Unary")
 , {65}tblEle(NT.T'.52, totoken."Unary" sub 1, Reduce*(27, T.64), Success*, "Unary")
 , {66}tblEle(T', totoken."(" sub 1, NT.67, T'.69, "(E)")
 , {67}tblEle(NT.29, totoken."E" sub 1, T.68, T'.69, "E)")
 , {68}tblEle(T, totoken.")" sub 1, Reduce.28, T'.69, ")")
 , {69}tblEle(T', totoken."[" sub 1, NT.70, NT.73, "[E]")
 , {70}tblEle(NT.29, totoken."E" sub 1, NT.71, NT.73, "E]")
 , {71}tblEle(NT.T.30, totoken."EL'" sub 1, T.72, NT.73, "]")
 , {72}tblEle(T, totoken."]" sub 1, Reduce.29, NT.73, "]")
 , {73}tblEle(NT.T'.15, totoken."String" sub 1, Reduce.30, NT.74, "String")
 , {74}tblEle(NT.T'.113, totoken."Declare" sub 1, NT.75, T'.77, "Declare E")
 , {75}tblEle(NT.154, totoken."Declare'" sub 1, NT.76, T'.77, "E")
 , {76}tblEle(NT.29, totoken."E" sub 1, Reduce.31, T'.77, "E")
 , {77}tblEle(T', totoken."if" sub 1, NT.78, NT.84, "if E then E else E")
 , {78}tblEle(NT.29, totoken."E" sub 1, T.79, NT.84, "E then E else E")
 , {79}tblEle(T, totoken."then" sub 1, NT.80, NT.84, "then E else E")
 , {80}tblEle(NT.29, totoken."E" sub 1, NT.81, NT.84, "E else E")
 , {81}tblEle(NT.T.104, totoken."IF" sub 1, T.82, NT.84, "else E")
 , {82}tblEle(T, totoken."else" sub 1, NT.83, NT.84, "else E")
 , {83}tblEle(NT.29, totoken."E" sub 1, Reduce.32, NT.84, "E")
 , {84}tblEle(NT.90, totoken."Name" sub 1, T.85, Fail, "Name(E)")
 , {85}tblEle(T, totoken."(" sub 1, NT.86, NT.89, "(E)")
 , {86}tblEle(NT.29, totoken."E" sub 1, NT.87, NT.89, "E)")
 , {87}tblEle(NT.T.30, totoken."EL'" sub 1, T.88, NT.89, ")")
 , {88}tblEle(T, totoken.")" sub 1, Reduce.33, NT.89, ")")
 , {89}tblEle(NT.90, totoken."Name" sub 1, Reduce.34, Fail, "Name")
 , {90}tblEle(NT.!T.94, totoken."Id" sub 1, T.91, Fail, "Id:Type")
 , {91}tblEle(T, totoken.":" sub 1, NT.92, NT.93, ":Type")
 , {92}tblEle(NT.109, totoken."Type" sub 1, Reduce.35, NT.93, "Type")
 , {93}tblEle(NT.!T.94, totoken."Id" sub 1, Reduce.36, Fail, "Id")
 , {94}tblEle(!T, totoken."," sub 1, Fail, !T.95, ", any")
 , {95}tblEle(!T, totoken."[" sub 1, Fail, !T.96, "[any")
 , {96}tblEle(!T, totoken."(" sub 1, Fail, !T.97, "(any")
 , {97}tblEle(!T, totoken."]" sub 1, Fail, !T.98, "]any")
 , {98}tblEle(!T, totoken.")" sub 1, Fail, !T.99, ")any")
 , {99}tblEle(!T, totoken.":" sub 1, Fail, !T.100, ":any")
 , {100}tblEle(!T, totoken."." sub 1, Fail, !T.101, ".any")
 , {101}tblEle(!T, totoken.dq sub 1, Fail, MatchAny.102, "dq any")
 , {102}tblEle(MatchAny, totoken."?" sub 1, Reduce.37, Fail, "any")
 , {103}tblEle(T, totoken."," sub 1, Reduce.38, Reduce.39, ",")
 , {104}tblEle(T, totoken."else" sub 1, T.105, Success*, "else if E then E")
 , {105}tblEle(T, totoken."if" sub 1, NT.106, Success*, "if E then E")
 , {106}tblEle(NT.29, totoken."E" sub 1, T.107, Success*, "E then E")
 , {107}tblEle(T, totoken."then" sub 1, NT.108, Success*, "then E")
 , {108}tblEle(NT.29, totoken."E" sub 1, Reduce*(40, T.104), Success*, "E")
 , {109}tblEle(NT.!T.94, totoken."Id" sub 1, T.110, Fail, "Id.Type")
 , {110}tblEle(T, totoken."." sub 1, NT.111, NT.112, ".Type")
 , {111}tblEle(NT.109, totoken."Type" sub 1, Reduce.41, NT.112, "Type")
 , {112}tblEle(NT.!T.94, totoken."Id" sub 1, Reduce.42, Fail, "Id")
 , {113}tblEle(T', totoken."let" sub 1, MatchAny.114, T'.118, "let any = E")
 , {114}tblEle(MatchAny, totoken."?" sub 1, T.115, T'.118, "any = E")
 , {115}tblEle(T, totoken."=" sub 1, NT.116, T'.118, "= E")
 , {116}tblEle(NT.29, totoken."E" sub 1, NT.117, T'.118, "E")
 , {117}tblEle(NT.T.103, totoken."comma?" sub 1, Reduce.43, T'.118, "")
 , {118}tblEle(T', totoken."assert" sub 1, NT.119, T'.123, "assert E report E")
 , {119}tblEle(NT.29, totoken."E" sub 1, T.120, T'.123, "E report E")
 , {120}tblEle(T, totoken."report" sub 1, NT.121, T'.123, "report E")
 , {121}tblEle(NT.29, totoken."E" sub 1, NT.122, T'.123, "E")
 , {122}tblEle(NT.T.103, totoken."comma?" sub 1, Reduce.44, T'.123, "")
 , {123}tblEle(T', totoken."{" sub 1, NT.124, T'.127, "{}")
 , {124}tblEle(NT.T.163, totoken."N" sub 1, T.125, T'.127, "}")
 , {125}tblEle(T, totoken."}" sub 1, NT.126, T'.127, "}")
 , {126}tblEle(NT.T.103, totoken."comma?" sub 1, Reduce.45, T'.127, "")
 , {127}tblEle(T', totoken."for" sub 1, NT.128, Fail, "for ForDeclare do E")
 , {128}tblEle(NT.139, totoken."ForDeclare" sub 1, T'.129, Fail, "ForDeclare do E")
 , {129}tblEle(T', totoken."do" sub 1, NT.130, T.134, "do E")
 , {130}tblEle(NT.29, totoken."E" sub 1, NT.131, T.132, "E")
 , {131}tblEle(NT.T.103, totoken."comma?" sub 1, Reduce.46, T.132, "")
 , {132}tblEle(T, totoken."for" sub 1, NT.133, Fail, "for ForDeclare while E do E")
 , {133}tblEle(NT.139, totoken."ForDeclare" sub 1, T.134, Fail, "ForDeclare while E do E")
 , {134}tblEle(T, totoken."while" sub 1, NT.135, Fail, "while E do E")
 , {135}tblEle(NT.29, totoken."E" sub 1, T.136, Fail, "E do E")
 , {136}tblEle(T, totoken."do" sub 1, NT.137, Fail, "do E")
 , {137}tblEle(NT.29, totoken."E" sub 1, NT.138, Fail, "E")
 , {138}tblEle(NT.T.103, totoken."comma?" sub 1, Reduce.47, Fail, "")
 , {139}tblEle(NT.!T.145, totoken."AccumList" sub 1, T.140, Fail, "AccumList, any ∈ E")
 , {140}tblEle(T, totoken."," sub 1, MatchAny.141, NT.144, ", any ∈ E")
 , {141}tblEle(MatchAny, totoken."?" sub 1, T.142, NT.144, "any ∈ E")
 , {142}tblEle(T, totoken."∈" sub 1, NT.143, NT.144, "∈ E")
 , {143}tblEle(NT.29, totoken."E" sub 1, Reduce.48, NT.144, "E")
 , {144}tblEle(NT.!T.145, totoken."AccumList" sub 1, Reduce.49, Fail, "AccumList")
 , {145}tblEle(!T, totoken."while" sub 1, Fail, MatchAny.146, "while any = E")
 , {146}tblEle(MatchAny, totoken."?" sub 1, T.147, Fail, "any = E")
 , {147}tblEle(T, totoken."=" sub 1, NT.148, Fail, "= E")
 , {148}tblEle(NT.29, totoken."E" sub 1, NT.149, Fail, "E")
 , {149}tblEle(NT.T.150, totoken."AccumList'" sub 1, Reduce.50, Fail, "")
 , {150}tblEle(T, totoken."," sub 1, MatchAny.151, Success*, ", any = E")
 , {151}tblEle(MatchAny, totoken."?" sub 1, T.152, Success*, "any = E")
 , {152}tblEle(T, totoken."=" sub 1, NT.153, Success*, "= E")
 , {153}tblEle(NT.29, totoken."E" sub 1, Reduce*(51, T.150), Success*, "E")
 , {154}
 tblEle(NT.T'.113, totoken."Declare" sub 1, Reduce*(52, NT.154), Success*, "Declare")
 , {155}tblEle(NT.MatchAny.159, totoken."FP" sub 1, NT.156, Fail, "FP")
 , {156}tblEle(NT.T.157, totoken."FPL'" sub 1, Reduce.53, Fail, "")
 , {157}tblEle(T, totoken."," sub 1, NT.158, Success*, ", FP")
 , {158}tblEle(NT.MatchAny.159, totoken."FP" sub 1, Reduce*(54, T.157), Success*, "FP")
 , {159}tblEle(MatchAny, totoken."?" sub 1, T.160, NT.162, "any:Type")
 , {160}tblEle(T, totoken.":" sub 1, NT.161, NT.162, ":Type")
 , {161}tblEle(NT.109, totoken."Type" sub 1, Reduce.55, NT.162, "Type")
 , {162}tblEle(NT.109, totoken."Type" sub 1, Reduce.56, Fail, "Type")
 , {163}tblEle(T, totoken."{" sub 1, NT.164, !T.166, "{}")
 , {164}tblEle(NT.T.163, totoken."N" sub 1, T.165, !T.166, "}")
 , {165}tblEle(T, totoken."}" sub 1, Discard*.T.163, !T.166, "}")
 , {166}tblEle(!T, totoken."}" sub 1, All, MatchAny.167, "}any")
 , {167}tblEle(MatchAny, totoken."?" sub 1, Discard*.T.163, All, "any")
 , {168}tblEle(!T, totoken.dq sub 1, All, !T.169, "dq any")
 , {169}tblEle(!T, totoken.colon sub 1, All, MatchAny.170, "colon any")
 , {170}tblEle(MatchAny, totoken."?" sub 1, Discard*.!T.168, All, "any")
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
else if place.a = {length of input}faili.top.stk.a then 'Match
else 'MatchPrefix

Function result(a:resultType) seq.symbol last.result.top.stk.a

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
  if inputi = endMark then {fail}next(rinfo, stk, Fstate.te, i, inputi, result, faili, failresult)
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