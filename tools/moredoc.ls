
 

<* section PEGgen *>

We will be transforming a seqencence of bytes into a sequence of words.

To do this we will use a special function /em PEGgen that will be recognized 
by the transform tool as a PEG grammar specification and automaticly generate code.  
To write the procedure we will need some other functions. To obtain these
function we start with the follow module.  


Module break2?

use standard

use bits

use seq.boolean

use seq.byte

use UTF8

use seq.char

function M(e:seq.word) byte
{how to convert a word in the grammar rule into a byte.In this case we use first char of the first letter of the first word}
let a = toint.first.decodeword.first.e,
tobyte.a

function toAttribute(a:seq.word, b:seq.byte) seq.word
{how to combine the last attribute with a subsequence of the input
to form a new attribute}
if isempty.b then "" else [encodeword.decodeUTF8.UTF8.b]

function PEGgen(seqElementType:byte, attributeType:seq.word) seq.boolean
empty:seq.boolean

<<<< Below is auto generated code >>>>

Since the module name ends in "?" pretty printing the result did not auto generate
this code which allows only the part of the generated code that is of interrest to be include here: 

function =(seq.word, byte) boolean true

function parse(myinput:seq.byte, table:seq.tblEle, initAttr:seq.word) runresult
stub

type reduction is toseq:seq.seq.word


function _(R:reduction, i:int) seq.word (toseq.R)_(i + 1)




Since the word PEG grammar is specified using words, a rule is need to
specify how a word should be translated into a byte.  For this example
we will use the rule:
<* block match2code ← dq / lf / cr / sp / any *> 

Now we need to specify an action for each segment of the rule which
will be a code fragment.  Below each segment is on a seperate line
with an = seperating the rule from the action.  
The arrow has been dropped. and the rule segment has been quoted.
<* block match2code ← dq / lf / cr / sp / any  
/br "match2code dq" = tobyte.34
/br ,"/ lf" = tobyte.10
/br ,"/ cr" = tobyte.13
/br ,"/ sp" = tobyte.32
 /br,"/ any" = M."/1"
*>

Here is a simplified PEGgrammar for transforming a sequence of words into a sequence of types.
<* block
  "* Words whitespace"  = R_0
/br "/ StandAlone" =R_0+R_1 
/br "/ Word" = R_0+R_1
/br "StandAlone +" ="+"
/br "WhiteSpace sp" = /Discard
/br "* Word  ! WhiteSpace ! StandAlone any" = /All
*>  

R  is a seq of the attributes constucted by the non-terminals in the rule. R_0
refers to the value of the attribute at the beginning of the rule.  

The action /Discard  throws away and result. 

The action /All  calls the function toAttribue   once for all matched bytes in the rule. 

The parameters of the special function PEGgen specifies this.

Now we can replace the previous  PEGgen function with the follow two function and
run the module through the transform function to get a module that will compile.

Function breakpara(myinput:seq.byte) seq.word
result.parse(myinput + tobyte.32, mytable, "")

function PEGgen(seqElementType:byte, attributeType:seq.word, R:reduction) seq.boolean
[
 "match2code dq" = tobyte.34
 , "/ lf" = tobyte.10
 , "/ cr" = tobyte.13
 , "/ sp" = tobyte.32
 , "/ any" = M."/1"
 , "* Words WhiteSpace" = R_0
 , "/ StandAlone" = R_0 + R_1
 , "/ Word" = R_0 + R_1
 , "StandAlone+" = "+"
 , "WhiteSpace sp" = /Discard
 , "* Word ! sp !+any" = /All
]




 

