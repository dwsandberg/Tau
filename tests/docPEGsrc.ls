/tag <h2> Using PEG  in Tau /tag </h2>

This document describes how to use Tau to create
 PEG grammars to parse the following seq of words:

function Example1 int let a = 1+2, a+(3+4) 

We assume the reader understands basic grammar terms such as parse tree, and non-terminal, terminal.

A PEG grammar to parses the above is  
<* block  G1 ← function any int E  
 /br E ← Sum  
 /br   Sum ← Atom Sum'  
 /br *  Sum' ← /sp+/sp Atom  
 /br   Atom ← (E)  
 /br /     let any = E, E 
 /br /    any  *>
 
/tag <h3> Using the PEG module /tag </h3>
 
 
 Tau provides a module PEG  for use a PEG grammar to
 transform a sequence of words into another sequence of words.
 An attribute will be passed in a post order transversal of the
 parse tree.  An action will be associated with each rule that
 specifies how to combined the attributes for each of the non-terminals in the
 rule to form a new rule.  The attributes of the  non-terminals
 will be specified with  $.1 $.2 $.3 ... 
 
 Rules that are repeated such as * Sum' above also may use $.0 which represents the return attribute of the last application of the rule.  It will be empty for the first interation of the rule. 
 
 The PEG module uses a string of words to specify the action
 and $.n is replaced with the attribute of the coresponding non-terminal. 
  
 The first example will produce the list of rules use in a post order transveral of
 the parse tree. Here is what the output should look like
 <* block
 Example1 a Atom ← any {1}
/br Atom ← any {2}
/br * Sum' ←+Atom
/br Sum ← Atom Sum'
/br E ← Sum
/br Atom ← any {a}
/br Atom ← any {3}
/br Atom ← any {4}
/br * Sum' ←+Atom
/br Sum ← Atom Sum'
/br E ← Sum
/br Atom ← (E)
/br * Sum' ←+Atom
/br Sum ← Atom Sum'
/br E ← Sum
/br Atom ← let any = E, E
/br Sum ← Atom Sum'
/br E ← Sum
/br G1 ← function any int E
 *> 
 The last line of this output will be produced by the action
 of the first rule of the grammar whoses action will be
 <* block
 $.1 $.2 G1 ← function any int E //br *>
 The any is treated as an non-terminal so $.1 refers to the word that any matches and $.2 refers to the attribute of E. Since /em /br will be used as a meta symbol in specifying the grammar /em //br with represent /em /br. 
 
 
Module PEGEx

use standard

use PEG

function input seq.word "function Example1 int let a = 1+2, a+(3+4)"

The PEG grammar above was transform into the string literal in postOrder function below by adding addint
a /em
/br before each line removing the arrow and adding an action.

Function postOrder seq.word
run(
 maketable."G1 function any int E /action $.1 $.2 G1 ← function any int E //br
 /br E Sum /action $.1 E ← Sum //br
 /br Sum Atom Sum' /action $.1 $.2 Sum ← Atom Sum' //br
 /br * Sum'+Atom /action $.0 $.1 * Sum' ←+Atom //br
 /br Atom (E) /action $.1 Atom ← (E) //br
 /br / let any = E, E /action $.1 $.2 $.3 Atom ← let any = E, E //br
 /br / any /action Atom ← any {$.1} //br"
 , input
)
 << 1

The << 1 in the last line above removes the status returned by the run function.

The function below is very similar to the above procedure but reverses the order of the lines in the output. 

Function ReversePostOrder seq.word
run(
 maketable."G1 function any int E /action G1 ← functionR any int E //br $.2 //br $.1
 /br E Sum /action E ← Sum //br $.1
 /br Sum Atom Sum' /action Sum ← Atom Sum' //br $.2 $.1
 /br * Sum'+Atom /action * Sum' ←+Atom //br $.1 $.0
 /br Atom (E) /action Atom ← (E) //br $.1
 /br / let any = E, E /action Atom ← let any = E, //br $.3 $.2 $.1
 /br / any /action Atom ← any {$.1} //br"
 , input
)
 << 1

By adding indentation to the ReversePostOrder we can represent theparse tree. The level of indentation indicates the level of the node in the parse. One detail is that the /em
/br after the /em *> ends up creating unwanted blank lines. To address this we use a second PEG grammar to remore the /em /br's after the /em *>.

Function parseTree seq.word
let a = run(
 maketable."G1 function any int E /action G1 ← functionR any int E <* block $.2 //br $.1 *>
 /br E Sum /action E ← Sum <* block $.1 *>
 /br Sum Atom Sum' /action Sum ← Atom Sum' <* block $.2 //br $.1 *>
 /br * Sum'+Atom /action * Sum' ←+Atom <* block $.1 //br $.0 *>
 /br Atom (E) /action Atom ← (E) <* block $.1 *>
 /br / let any = E, E /action Atom ← let any = E, E <* block $.3 //br $.2 //br $.1 *>
 /br / any /action Atom ← any {$.1}"
 , input
),
run(
 maketable."* S *> B /action $.0 *>
 /br / any /action $.0 $.1
 /br * B //br /action"
 , a
)
 << 2

The output of the parseTree is: 

G1 ← functionR any int E <* block E ← Sum <* block Sum ← Atom Sum' <* block /br Atom ← let any = E, E <* block E ← Sum <* block Sum ← Atom Sum' <* block * Sum' ←+Atom <* block Atom ← (E) <* block E ← Sum <* block Sum ← Atom Sum' <* block * Sum' ←+Atom <* block Atom ← any {4} /br *> Atom ← any {3} *> *> *> *> Atom ← any {a} *> *> E ← Sum <* block Sum ← Atom Sum' <* block * Sum' ←+Atom <* block Atom ← any {2} /br *> Atom ← any {1} *> *> a *> *> *> Example1 *>

The stkCode function below creates  postfix code for a simple stack machine.  The output is <* block 1 2 Add Store a a 3 4 Add Add *>

Function stkCode seq.word
run(
 maketable."G1 function any int E /action  $.2
 /br E Sum /action $.1
 /br Sum Atom Sum' /action $.1 $.2
 /br * Sum'+Atom /action $.0 $.1 Add
 /br Atom (E) /action $.1
 /br / let any = E, E /action $.2 Store $.1 $.3
 /br / any /action $.1"
 , input
)
 << 1

A PEGdebug tool is provide that will give the detail steps in the parse using the PEG module. The output of the debug tool for the parse in postfix function is provided here but no explanation of the output is provided here. 

/tag <h3> Using genPEG    /tag </h3>

The  transform tool can generate code for a function /em parse  that
allows allows code to be written equivalent to the stkCode function above.

Function stkCode2 seq.word 
result.parse(input, {initail Attribute }"" )

Below is a function genPEG that the transform tool replaces any code after that procedure will auto generated code. One function that will be generated is <* block  Function    parse(input:seq.seqElementType, attributeType) runresultType *>  In this case the
seqElementType is word and the attributeType is seq.word.  
The parse function executes that actions of the rules in the order of the post order trasversal of the parse tree.  Each action comibines the attributes matching the Non-terminals of the rule into a single attribute. 
 
We need to supply a couple of functions before giving the genPEG procedure. 

function endMark word  {Specifies the seqElement that marks the end of the input. For UTF8 input we use an illegal byte in UTF8 format. } encodeword.[char.254]

function  toAttribute(attribute:seq.word, seqElement:seq.word)seq.word 
{This is used to form the attribute for the "any" in a rule by calling toAttribute(<current attribute> ,[<the element  "any" matches>]./br This function is also call when starting a * or + Non-terminal. In this case the seqElement is the
empty sequence  } 
seqElement
 

use seq.word

Since any code after the genPEG procedure is replace with auto generated code we also give
a procedure that allows us to see the output of the examples above.

Function PEGex seq.word
{COMMAND}
stkCode2+"/br"+
stkCode
 + "/tag <hr>"
 + postOrder
 + "/tag <hr>"
 + ReversePostOrder
 + "/tag <hr>"
  + parseTree


The body of the PEGprocedure is formed taking the string in the stkCode procedure and making the folowing changes:
/br quote each rule and action,  /br change /action to = , change /em /br to a comma
/br
change $.1 to :($.1) and do the same for the other $ expressions. 

function genPEG(seqElementType:word, attributeType:seq.word) seq.boolean
{wordmap: dq dq , //br /br,  " $" sub 1 }
 ["G1 function any int E " = "  :($.2)"
," E Sum " = " :($.1)"
," Sum Atom Sum' " = " :($.1) :($.2)"
," * Sum'+Atom " = " :($.0) :($.1) Add"
," Atom (E) " = " :($.1)"
," / let any = E, E " = " :($.2) Store :($.1) :($.3)"
," / any " = " :($.1)"]

The comment in the genPEG procedure is significate as it sepecifies how to map a word in a rule into the attributeType. Following the = is
a comma seperated list. if the word of the rule matches  first word of the element in the list it will be replaced with the remainer of the words in the element.  The last element of the list is the default case and is used if word of the rule does not match any of the other elements.  In the default case the whole element is used and  the $ is replaced with the word of the rule. 
  




/tag <h4> Using a symbol table  /tag </h4>


Next we will add a check to see that all references are define. The following should produce
an error <* block function Example1 int let a = 1+2, b+(3+4) *>
since /em b is not defined.

We start fresh with a new module.

Module PEGEx2

use standard

use set.word

use UTF8

use seq.word
 
function input seq.word "function Example1 int let a = 1+2, b+(3+4)"


function endMark word   encodeword.[char.254]

Instead of using seq.word as the attributeType we use

type attribute is symbols:set.word, code:seq.word

function toAttribute(a:attribute, b:seq.word) attribute
attribute(symbols.a, b)

Notice that this passes allong the symbols of the previous attribute unlike the toAttribute in the last section which ignored the previous attribute. 


Function stkCode3  seq.word
{COMMAND}
let initAttribute=attribute(asset."1 2 3 4","")
let finalAttribute=result.parse(input,initAttribute )
code.finalAttribute

A change is needed to modify the rule " / let any = E, E " as  an action  is needed to add a  symbol to the symbol table     before the symbol is referenced.  Below this rule is replaced with   " / Declare, E " and  "Declare any=E" is added. The action of the second rule will add a value to the symbol table.  Also,  check in  action of the "/ any" rule is added to raise an error if the symbol is not define.

These changes have been made to   the genPEG  below. Calling stkCode3 will now
raise the error <* block Not defined b *>

 
function genPEG(seqElementType:word, attributeType:attribute) seq.boolean
{wordmap: " $" sub 1}
[
 "G1 function any int E" = $.2
 , "E Sum" = $.1
 , "Sum Atom Sum'" = attribute(symbols.$.0, code.$.1 + code.$.2)
 , "* Sum'+Atom" = attribute(symbols.$.0, code.$.0 + code.$.1 + "Add")
 , "Atom (E)" = $.1
 , "/ Declare E" = attribute(symbols.$.0, code.$.1 + code.$.2)
 , "/ any" = assert  (code.$.1) sub 1 ∈ symbols.$.1 report "Not defined:(code.$.1)"
 attribute(symbols.$.0  , code.$.0 +  code.$.1 )
 , "Declare let any = E,"
  = attribute(symbols.$.0 +  (code.$.1) sub n.code.$.1, code.$.2 + "Store" + code.$.1 )
]


/tag <h4> Adding Error Recover  /tag </h4>


This section  describes how   to locate  the location of the error where
a parse fails.  The same grammar is used as in the section above with an rule added
for if-then-else. The   module in this section  runs mulitple examples and traps any raised errors when processing the
the example.   


This example uses many options of genPEG.  Here is a summary of what the options do: 

<* table 
/row /strong Option    /cell /strong Value /cell /strong Purpose
/row seqElementType  /cell type /cell  the element type of the sequence to be parsed
/row attributeType /cell type  /cell   the type of the attribute constructed by the parse.
/row resultType: type  /cell the tyoe name to be used for the  results of the parse.
commonType type /cell type of an immutable  value that will be available through out the
parse. This value is supplied in an parameter of the parse. 
/row commonName /cell word  /cell The name to use in an action to reference the above
immutable value. When using this option also include in the parameters of genPEG a parameter of the form
commonName:commmonType
/row wordmap  /cell map value /cell How to map a  terminal in rule to a element of the sequence to be parsed  
/row error  /cell flag /cell include information for pin pointing where the parse failed.
*>

An option may be specified in the parameter list of genPEG or in the first comment of genPEG
<* table
/row /strong Kind  /cell /strong As /strong parameter /cell /strong In /strong comment 
/row type  /cell    option:value  /cell comment:type
/row word  /cell  /cell   option=value
/row flag    /cell option:boolean /cell option=
/row map value /cell /cell  option= comma seperated list.
*>

The resultType  may have the following fields:
<* block
/br result: the final attribute
/br status:    one of the words Match, MatchPrefix, or Failed.
/br place:     the first unprocess element of the input. 
/br input:     the input sequence including the endMark.
/br recoveryEnding: On failure, a sequence of words that can be added to the input  
of the successfully parsed elements of the input to form a string that can be parsed. 
*>

The recoveryEnding also provides a way to construct a input that can be parsed.  In this section we use the same parser to parse it again.  But to do a successful parse 
the semantic checking must not be done.  This example use the
  commonName and commonType options to add a parameter to the parse to turn semantic checking on or off.    In the Tau implementation instead of use the same parser a second parser is used that  pretty prints the input.  


Here are  thedescription of the examples used     the output they give.
The first line of the ouput is the input to the parse 
<* block
Example of a successful parse.
<* block  function Example1 int let a = 1+2, a+(3+4)
status: Match place:18 code:1 2 Add Store a a 3 4 Add Add 
*>
Example of a   parse with extra words at the end.
<* block
function Example2 int let a = 1+2, a+(3+4) extra words
status: MatchPrefix place:18 code:1 2 Add Store a a 3 4 Add Add
*>
Example of a  Failed parse  that never executes an action.
<* block
function Example3 int let
status:Failed place:0 code:
*>
Example of a semantic error:
<* block
function Example4 int let a = 1+2, (((b)))+(3+4)
Error at 15 message:b is not defined. To finish parse, ')))+(3+4) ' was replaced with '))) '
*>
Another example of a successful parse
<* block
function Example5 int if 1 then 2+3 else 4
status: Match place:12 code:1 2 3 Add 4 If
*>
Example of parse that failed and then backtrack ending up match none of the rule, The maxinum
the maxium place in the input where a reduce was done was used as  recovery point.  In this example
the recover point is a the  reduction of 2+3.
<* block
function Example6 int if 1 then 2+3 else
Failed Error at 10 message:syntax error. To finish parse, ' else ' was replaced with ' else any '
*> *>




Module PEGEx3

use standard

use set.word

use UTF8

use seq.word

function endMark word   encodeword.[char.254]

type attribute is symbols:set.word, code:seq.word

function toAttribute(a:attribute, b:seq.word) attribute
attribute(symbols.a, b)

use process.seq.word

Function stkCode4  seq.word
{COMMAND}
 let data=["function Example1 int let a = 1+2, a+(3+4)"
    ,"function Example2 int let a = 1+2, a+(3+4) extra words"
    ," function Example3 int let"
     ,"function Example4 int let a = 1+2, (((b)))+(3+4)"
           , " function Example5 int  if 1 then 2+3 else 4"
      ," function Example6 int  if 1 then 2+3 else "
     ]
  for acc="" , in ∈ data do
   let p = process.parser.in
  acc+" :((in)/br"+ if aborted.p then 
message.p+"/br"
   else  result.p+"/br"  
  acc           

function parser(in:seq.word) seq.word
let initAttribute=attribute(asset."1 2 3 4","")
let p=parse(in,initAttribute ,true)
let finalAttribute=result.p
if status.p ∈ "Failed" ∧ place.p > 0 then
"Failed"+errormessage("syntax error",recoverInfo(pop.stk.p,input.p,place.p,faili.p))
else 
"status::(status.p) place::(place.p) code:" +code.finalAttribute

  
function errormessage(message:seq.word,rinfo:recoverInfo) seq.word
{provides a uniform way to generate an error message within an action}
let ending = recoveryEnding.rinfo
let corrected = subseq(input.rinfo, 1, place.rinfo - 1) + ending
 let reparse = parse(corrected, attribute(empty:set.word,""),false),
if status.reparse ∉ "Match" then
"Failed reparse" + corrected
else  "Error at:(place.rinfo) message::(message). To finish parse,':(subseq(input.rinfo , place.rinfo   , n.input.rinfo-1) ) 
' was replaced with ':(ending)'"
 

function genPEG(seqElementType:word, attributeType:attribute, resultType:recoverInfo, rinfo:recoverInfo,
commonType:boolean,checkSemantics:boolean) seq.boolean
{commonName: checkSemantics error:   wordmap :   " $" sub 1}
[ 
 "G1 function any int E" = $.2
 , "E   if E then E  else E" = 
 attribute(symbols.$.0,  code.$.1+code.$.2+code.$.3+" If")
 , "/ Sum" = $.1
 , "Sum Atom Sum'" = attribute(symbols.$.0, code.$.1 + code.$.2)
 , "* Sum'+Atom" = attribute(symbols.$.0, code.$.0 + code.$.1 + "Add")
 , "Atom (E)" = $.1
 , "/ Declare E" = attribute(symbols.$.0, code.$.1 + code.$.2)
 , "/ ! if ! let any" = assert not.checkSemantics ∨ (code.$.1) sub 1 ∈ symbols.$.1 report errormessage(":(code.$.1) is not defined ",rinfo)
 attribute(symbols.$.0  , code.$.0 +  code.$.1 )
 , "Declare let any = E,"
  = attribute(symbols.$.0 +  (code.$.1) sub n.code.$.1, code.$.2 + "Store" + code.$.1 )
]

