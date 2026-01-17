

Using PEG in Tau /h2

This document describes how to use Tau to create PEG grammars to parse the following sequence of words:

function Example1 int
let a = 1 + 2,
a + (3 + 4)

We assume the reader understands basic grammar terms such as parse tree, non-terminal, and terminal.

A PEG grammar to parse the above is // G1 ← function any int E /br
E ← Sum /br
Sum ← Atom Sum' /br
* Sum' ←+Atom /br
Atom ← (E) /br
/ let any = E, E /br
/ any /block

Using the PEG module /h3

Tau provides a module named PEG for using a PEG grammar to transform a sequence of words into another sequence of words. An attribute will be passed in a post-order traversal of the parse tree. An action will be associated with each rule that specifies how to combine the attributes for each of the non-terminals in the rule to form a new rule. The attributes of the non-terminals will be referenced as $.1, $.2, $.3,... 

Rules that are repeated, such as * Sum' above, may also use $.0 which represents the return attribute of the last application of the rule. It will be empty for the first iteration of the rule. 

The PEG module uses a string of words to specify the action, and $.n is replaced with the attribute of the corresponding non-terminal. 

The first example will produce the list of rules used in a post-order traversal of the parse tree. Here is what the output should look like // Example1 a Atom ← any {1} /br
Atom ← any {2} /br
* Sum' ←+Atom /br
Sum ← Atom Sum' /br
E ← Sum /br
Atom ← any {a} /br
Atom ← any {3} /br
Atom ← any {4} /br
* Sum' ←+Atom /br
Sum ← Atom Sum' /br
E ← Sum /br
Atom ← (E) /br
* Sum' ←+Atom /br
Sum ← Atom Sum' /br
E ← Sum /br
Atom ← let any = E, E /br
Sum ← Atom Sum' /br
E ← Sum /br
G1 ← function any int E /block

The last line of this output will be produced by the action of the first rule of the grammar whose action will be // $.1 $.2 G1 ← function any int E //br /block The any /em is treated as a non-terminal so $.1 refers to the word that any /em matches and $.2 refers to the attribute of E. Since '/br' is used as a meta symbol in specifying the grammar, '//br' will represent '/br'. 

Module PEGEx

use standard

use PEG

function input seq.word "function Example1 int let a = 1+2, a+(3+4)"

The PEG grammar above was transformed into the string literal in the postOrder function below by adding a '/br' before each line, removing the arrow, and adding an action.

Function postOrder seq.word
run(
 maketable."G1 function any int E /action $.1 $.2 G1 ← function any int E //br /br
 E Sum /action $.1 E ← Sum //br /br
 Sum Atom Sum' /action $.1 $.2 Sum ← Atom Sum' //br /br
 * Sum'+Atom /action $.0 $.1 * Sum' ←+Atom //br /br
 Atom (E) /action $.1 Atom ← (E) //br /br
 / let any = E, E /action $.1 $.2 $.3 Atom ← let any = E, E //br /br
 / any /action Atom ← any {$.1} //br"
 , input
)
<< 1

The << 1 in the last line above removes the status returned by the run function.

The function below is very similar to the above procedure, but reverses the order of the lines in the output. 

Function ReversePostOrder seq.word
run(
 maketable."G1 function any int E /action G1 ← functionR any int E //br $.2 //br $.1 /br
 E Sum /action E ← Sum //br $.1 /br
 Sum Atom Sum' /action Sum ← Atom Sum' //br $.2 $.1 /br
 * Sum'+Atom /action * Sum' ←+Atom //br $.1 $.0 /br
 Atom (E) /action Atom ← (E) //br $.1 /br
 / let any = E, E /action Atom ← let any = E, //br $.3 $.2 $.1 /br
 / any /action Atom ← any {$.1} //br"
 , input
)
<< 1

By adding indentation to the ReversePostOrder, we can represent the parse tree. The level of indentation indicates the node's position in the parse tree. 

use PEGparse


Function parseTree seq.word
 run(
maketable("G1 function any int E /action G1 ← functionR any int E // $.2 //br $.1 /block /br
  E Sum /action E ← Sum // $.1 /block /br
  Sum Atom Sum' /action Sum ← Atom Sum' // $.2 //br $.1 /block /br
  * Sum'+Atom /action * Sum' ←+Atom // $.1 //br $.0 /block /br
  Atom (E) /action Atom ← (E) // $.1 /block /br
  / let any = E, E /action Atom ← let any = E, E // $.3 //br $.2 //br $.1 /block /br
  / any /action Atom ← any {$.1}"
), input
 ) << 1
 
 

The output of the parseTree is: 

G1 ← functionR any int E // E ← Sum // Sum ← Atom Sum' // /br
Atom ← let any = E, E // E ← Sum // Sum ← Atom Sum' // * Sum' ←+Atom // Atom ← (E) // E ← Sum // Sum ← Atom Sum' // * Sum' ←+Atom // Atom ← any {4} /br
/block Atom ← any {3} /block /block /block /block Atom ← any {a} /block /block E ← Sum // Sum ← Atom Sum' // * Sum' ←+Atom // Atom ← any {2} /br
/block Atom ← any {1} /block /block a /block /block /block Example1 /block

The stkCode function below creates postfix code for a simple stack machine. The output is // 1 2 Add Store a a 3 4 Add Add /block

Function stkCode seq.word
run(
 maketable."G1 function any int E /action $.2 /br
 E Sum /action $.1 /br
 Sum Atom Sum' /action $.1 $.2 /br
 * Sum'+Atom /action $.0 $.1 Add /br
 Atom (E) /action $.1 /br
 / let any = E, E /action $.2 Store $.1 $.3 /br
 / any /action $.1"
 , input
)
<< 1

The PEGdebug tool provides detailed steps of the parse. The debug tool output for the parse of the postfix function is provided //    here  // ./PEGdebugEx.html /href /a, but no explanation of the output is provided. 

Using genPEG /h3

The transform tool can generate code for a function // parse /em that allows code to be written equivalent to the stkCode function above.  

Function stkCode2 seq.word result.parse(input, {initail Attribute} "")

Below is a function genPEG that the transform tool replaces any code after that procedure with auto-generated code. One function that will be generated is // Function parse (input:seq.seqElementType, attributeType) runresultType /block In this case, the seqElementType is word /em, and the attributeType is // seq.word /em . The parse function executes the actions of the rules in the order of the post-order traversal of the parse tree. Each action combines the attributes matching the Non-terminals of the rule into a single attribute. 

We need to supply a couple of functions before giving the genPEG procedure. 

function endMark word
{Specifies the seqElement that marks the end of the input. For UTF8 input we use an illegal byte in UTF8 format. }
encodeword.[char.254]

function toAttribute(attribute:seq.word, seqElement:seq.word) seq.word
{This is used to form the attribute for the any /em in a rule by calling toAttribute (<current attribute>, [<the element" any" matches>]. This function is also called when starting a * or /sp + /sp Non-terminal. In this case, the seqElement is the empty sequence.}
seqElement

use seq.word

Any code after the genPEG procedure is replaced with auto-generated code.  Because of this any user defined function must be before the genPEG procedure.  The function below shows the output of the functions above.

Function PEGex seq.word
{COMMAND}
{ stkCode
 + "/hr"
 + } ":(postOrder) /p  :(ReversePostOrder) /p :(stkCode) "
+
 "/p :(parseTree)"
 

The body of the PEGprocedure is formed by taking the string in the stkCode procedure and making the following changes: 

//ol quote each rule and action /li
change /action to =, change   / /nsp br  to a comma /li
change $.1 to:($.1) and do the same for the other $ expressions. /li /ol

function genPEG(seqElementType:word, attributeType:seq.word) seq.boolean
{wordmap: dq dq, " $" sub 1}
[
 "G1 function any int E" = ":($.2)"
 , "E Sum" = ":($.1)"
 , "Sum Atom Sum'" = ":($.1):($.2)"
 , "* Sum'+Atom" = ":($.0):($.1)Add"
 , "Atom (E)" = ":($.1)"
 , "/ let any = E, E" = ":($.2)Store:($.1):($.3)"
 , "/ any" = ":($.1)"
]

The comment in the genPEG procedure is significant as it specifies how to map a word in a rule into the attributeType. Following the = is a comma-separated list. If the word of the rule matches the first word of the element in the list, it will be replaced with the remainder of the words in the element. The last element of the list is the default case and is used if the word in the rule does not match any of the other elements. In the default case, the entire element is used, and $ is replaced with the rule's word. 

 Using a symbol table /h4

Next, we will add a check to see that all references are defined. The following should produce an error // function Example1 int /br let a = 1+2,  /br b+(3+4) /block since // b /em is not defined.

We start fresh with a new module.

Module PEGEx2

use standard

use set.word

use UTF8

use seq.word

function input seq.word "function Example1 int let a = 1+2, b+(3+4)"

function endMark word encodeword.[char.254]

Instead of using seq.word as the attributeType we use

type attribute is symbols:set.word, code:seq.word

function toAttribute(a:attribute, b:seq.word) attribute attribute(symbols.a, b)

Notice toAttribute passes along the symbols of the previous attribute, unlike the toAttribute in the last section, which ignored the previous attribute. 

Function stkCode3 seq.word
{COMMAND}
let initAttribute = attribute(asset."1 2 3 4", "")
let finalAttribute = result.parse(input, initAttribute),
code.finalAttribute

The rule" / let any = E, E"   to add a symbol to the symbol table before the symbol is referenced. Below this rule," / Declare, E" is replaced with" Declare any = E", and" Declare any = E" is added. The action of the second rule will add a value to the symbol table. Also, check in action of the" / any" rule is added to raise an error if the symbol is not defined.

These changes have been made to the genPEG below. Calling stkCode3 will now raise the error // Not defined b /block

function genPEG(seqElementType:word, attributeType:attribute) seq.boolean
{wordmap: " $" sub 1}
[
 "G1 function any int E" = $.2
 , "E Sum" = $.1
 , "Sum Atom Sum'" = attribute(symbols.$.0, code.$.1 + code.$.2)
 , "* Sum'+Atom" = attribute(symbols.$.0, code.$.0 + code.$.1 + "Add")
 , "Atom (E)" = $.1
 , "/ Declare E" = attribute(symbols.$.0, code.$.1 + code.$.2)
 , "/ any"
 = assert (code.$.1) sub 1 ∈ symbols.$.1 report "Not defined:(code.$.1)",
 attribute(symbols.$.0, code.$.0 + code.$.1)
 , "Declare let any = E,"
 = attribute(symbols.$.0 + (code.$.1) sub n.code.$.1, code.$.2 + "Store" + code.$.1)
]

 Adding Error Recover /h4

This section describes how to determine the location of the parse error. The same grammar is used as in the section above, with a rule added for if-then-else. The module in this section runs multiple examples and traps any errors that arise during processing. 

This example uses many genPEG options. Here is a summary of what the options do: 

// /td /tr
// Option /strong /td // Value /strong /td // Purpose /strong /td /tr
seqElementType /td type /td the element type of the sequence to be parsed /td /tr
attributeType /td type /td the type of the attribute constructed by the parse./td /tr
resultType: type /td the type name to be used for the results of the parse.commonType type /td type of an immutable value that will be available throughout the parse. This value is supplied as a parameter of the parse. /td /tr
commonName /td word /td The name to use in an action to reference the above immutable value. When using this option also include in the parameters of genPEG a parameter of the form commonName: commonType /td /tr
wordmap /td map value /td How to map a terminal in rule to an element of the sequence to be parsed /td /tr
error /td flag /td include information for pinpointing where the parse failed./td /tr
/table

An option may be specified in the parameter list of genPEG or in the first comment of genPEG // /td /tr
// Kind /strong /td // As /strong // parameter /strong /td // In /strong // comment /strong /td /tr
type /td option:value /td comment:type /td /tr
word /td /td option = value /td /tr
flag /td option:boolean /td option = /td /tr
map value /td /td option = comma seperated list./td /tr
/table

The resultType may have the following fields:// /br
result: the final attribute /br
status: one of the words Match, MatchPrefix, or Failed./br
place: the first unprocessed element of the input. /br
input: the input sequence including the endMark./br
recoveryEnding: On failure, a sequence of words that can be added to the input of the successfully parsed elements of the input to form a string that can be parsed. /block

The recoveryEnding also provides a way to construct an input that can be parsed. In this section, we use the same parser to parse it again. But to do a successful parse, the semantic checking must not be done. This example uses the commonName and commonType options to add a parameter to the parse to turn semantic checking on or off. In the Tau implementation, instead of using the same parser, a second parser is used to pretty-print the input. 

Here is the description of the examples used, and the output they give. The first line of the output is the input to the parser// Example of a successful parse.// function Example1 int let a = 1+2, a+(3+4) status: Match place:18 code:1 2 Add Store a a 3 4 Add Add /block Example of a parse with extra words at the end.// function Example2 int let a = 1+2, a+(3+4) extra words status: MatchPrefix place:18 code:1 2 Add Store a a 3 4 Add Add /block Example of a Failed parse that never executes an action.// function Example3 int let status:Failed place:0 code:/block Example of a semantic error:// function Example4 int let a = 1+2, (((b)))+(3+4) Error at 15 message:b is not defined. To finish parse, ')))+(3+4) ' was replaced with '))) ' /block Another example of a successful parse // function Example5 int if 1 then 2+3 else 4 status: Match place:12 code:1 2 3 Add 4 If /block Example of parse that failed and then backtrack ending up match none of the rule, The maxinum the maxium place in the input where a reduce was done was used as recovery point. In this example the recover point is a the reduction of 2+3.// function Example6 int if 1 then 2+3 else Failed Error at 10 message:syntax error. To finish parse, ' else ' was replaced with ' else any ' /block /block

Module PEGEx3

use standard

use set.word

use UTF8

use seq.word

function endMark word encodeword.[char.254]

type attribute is symbols:set.word, code:seq.word

function toAttribute(a:attribute, b:seq.word) attribute attribute(symbols.a, b)

use process.seq.word

Function stkCode4 seq.word
{COMMAND}
let data =
 [
  "function Example1 int let a = 1+2, a+(3+4)"
  , "function Example2 int let a = 1+2, a+(3+4) extra words"
  , "function Example3 int let"
  , "function Example4 int let a = 1+2, (((b)))+(3+4)"
  , "function Example5 int if 1 then 2+3 else 4"
  , "function Example6 int if 1 then 2+3 else"
 ]
for acc = "", in ∈ data
do
 let p = process.parser.in,
 acc + ":((in)" + if aborted.p then message.p + "" else result.p + "",
acc

function parser(in:seq.word) seq.word
let initAttribute = attribute(asset."1 2 3 4", "")
let p = parse(in, initAttribute, true)
let finalAttribute = result.p,
if status.p ∈ "Failed" ∧ place.p > 0 then "Failed" + errormessage("syntax error", recoverInfo(pop.stk.p, input.p, place.p, faili.p))
else "status::(status.p)place::(place.p)code:" + code.finalAttribute

function errormessage(message:seq.word, rinfo:recoverInfo) seq.word
{provides a uniform way to generate an error message within an action}
let ending = recoveryEnding.rinfo
let corrected = subseq(input.rinfo, 1, place.rinfo - 1) + ending
let reparse = parse(corrected, attribute(empty:set.word, ""), false),
if status.reparse ∉ "Match" then "Failed reparse" + corrected
else "Error at:(place.rinfo)message::(message). To finish parse, ':(subseq(input.rinfo, place.rinfo, n.input.rinfo - 1))' was replaced with ':(ending)'"

function genPEG(
seqElementType:word
, attributeType:attribute
, resultType:recoverInfo
, rinfo:recoverInfo
, commonType:boolean
, checkSemantics:boolean
) seq.boolean
{commonName: checkSemantics error: wordmap: " $" sub 1}
[
 "G1 function any int E" = $.2
 , "E if E then E else E" = attribute(symbols.$.0, code.$.1 + code.$.2 + code.$.3 + "If")
 , "/ Sum" = $.1
 , "Sum Atom Sum'" = attribute(symbols.$.0, code.$.1 + code.$.2)
 , "* Sum'+Atom" = attribute(symbols.$.0, code.$.0 + code.$.1 + "Add")
 , "Atom (E)" = $.1
 , "/ Declare E" = attribute(symbols.$.0, code.$.1 + code.$.2)
 , "/ ! if ! let any"
 = assert not.checkSemantics ∨ (code.$.1) sub 1 ∈ symbols.$.1 report errormessage(":(code.$.1)is not defined", rinfo),
 attribute(symbols.$.0, code.$.0 + code.$.1)
 , "Declare let any = E,"
 = attribute(symbols.$.0 + (code.$.1) sub n.code.$.1, code.$.2 + "Store" + code.$.1)
] 