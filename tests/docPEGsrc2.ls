

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

odule PEGEx

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
{wordmap: dq dq, //br /br," $" sub 1}
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
