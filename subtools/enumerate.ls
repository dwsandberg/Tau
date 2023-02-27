Module enumerate

use file

use seq.file

use pretty

use standard

use textio

use sparseseq.word

Function enumerate(input:seq.file, o:seq.word) seq.file
{* The /keyword enumeration cmd is used to generate code in a module for enumeration types instead of creating
the code by hand. If the following in a file named enum.ls it will generate two enumeration types and
operations on them.
/p ____________________
/p  Module enumerate
/p  use standard
/p  enumerationtype = numbers data = ? one two three four five
/p  enumerationtype = byte decodename = twodecode flags = nodecs withvalues data = 0 two0 2 two1 4 two2
8 two3 10 two4 20 two5
/p ___________________
/p  Here is a link to the <* none <a href ="./install4.html" > Result </a> *>
/p  In the first enumeration type Each word in the data list is given a value starting with 0. The ?
mark is a place holder for numbers that with not be include in the type.
/p  The second example uses and existing data type byte. Because of this the /keyword nodecs flag is supplied
which indicates the declaration of the type will not be generated. The flag /keyword withvalues indicates the
data list contains the hex value of the constant follow by the name.
}let message = "The data below this line was auto generated.",
for data = "", auto = "", continue = true, p ∈ breakparagraph.data.first.input
while continue
do
 if p = message then
  next(data, auto, false)
 else if subseq(p, 1, 2) = "enumerationtype =" then
  next(data + "/p" + p
   , auto
   + enumerate(extractValue(p, "enumerationtype")
    , extractValue(p, "data")
    , "withvalues"_1 ∈ extractValue(p, "flags")
    , "nodecs"_1 ∈ extractValue(p, "flags")
    , extractValue(p, "decodename"))
   , true)
 else
  next(
   data + if subseq(p, 1, 1) ∈ ["Function", "function"] then pretty.p else p /if + "/p"
   , auto
   , true)
/do
 [
  file(filename.o
   , data + "/p" + message
   + "/p_________________________________________"
   + auto >> 1)
  ]


function enumerate(type:seq.word
 , codes0:seq.word
 , withvalues:boolean
 , nodefs:boolean
 , decodename:seq.word) seq.word
let codes = 
 if withvalues then
  for acc = sparseseq."?"_1, state = 1, code = first.codes0, w ∈ codes0 << 1 do
   if state = 1 then
    next(replaceS(acc, toint.merge("0x" + code) + 1, [w]), 0, code)
   else
    next(acc, 1, w)
  /do for txt = "", e ∈ acc do txt + e /do txt
 else
  codes0
,
if nodefs then
 ""
else
 "/p type $(type) is toint:int
  /p Export toint ($(type)) int
  /p Export $(type) (i:int) $(type)
  /p Export type:$(type)
  /p $(pretty."Function = (a:$(type), b:$(type)) boolean toint.a = toint.b")"
/if
+ for acc = "", list = "let discard = [", i ∈ arithseq(length.codes, 1, 1) do
 if codes_i = "?"_1 then
  next(acc, list)
 else
  next(acc + "/p Function" + codes_i + type + type + "." + toword(i - 1)
   , list + codes_i + ",")
/do
 acc + "/p"
 + pretty("Function $(if isempty.decodename then "decode" else decodename) (code:$(type)) seq.word
  $(list >> 1)] let i = toint.code, if between (i+1, 1,"
 + toword.length.codes
 + ") then let r = [$(dq.codes)_(i+1)],"
 + "if r ≠ $(dq."?") then r else $(dq(type + "."))+toword.i else $(dq(type + "."))
  +toword.i")
 + "/p" 