

//../daws/codeexample.css /link

The Tau Programming Language /h1

Programming languages today look pretty much the same as they did 30 years ago. Today, they may have a few more features, but they are not substantially better as a notation for thought. I have created another programming language in an attempt to introduce a new way of thinking about programming. 

This new language is different because there is:

No assignment operator. /li

No loop/while statement /li

No function type. /li

Only uses program state in a very controlled way. /li

Words are the basic text element instead of characters. /li

Heavy use of sequences. /li

Introduces a new control structure for iterating through loops. /li /ul

Functional programming languages have no assignment operator or loop statements, but tend to be based on the lambda calculus, which uses higher-order functions. We only include the basic operations for functions—declaring, calling, and binding an unbound function to an actual function in an instantiation of a parameterized module. 

Functional languages tend to use recursion to replace loop control structures. The full power of recursion is seldom needed. We introduce a new control structure to cover many simple uses of recursion. 

Instructions for downloading and installing Tau in // // installdoc.html /href here /a to try out the examples below for yourself. 

Basic Structure /h2

Tau is word-based rather than character-based. A source file for Tau is UTF-8 encoded. Blank lines in the file break the file into a sequence of paragraphs. Spaces separate words. Some characters, such as '+', form a word of a single character even when there is no space before or after. Paragraphs are further grouped into modules /em. 

Converting UTF-8 to a sequence of paragraphs /h3

Tau transforms the bytes a UTF-8 encoded file into a sequence of paragraphs by classifying the bytes into 5 groups. 

The LF group is the ASCII linefeed character. /li

The Space group is the ASCII space and the carriage return. The carriage return is added to handle the end-of-line representation in DOS. /li

The StandAlone group is the ASCII characters ()+,-..:= [] {} and the double quote. /li

The other group, which contains any byte not included in the other three groups. /li /ol

By considering the class of each byte (the current byte) and the next byte (the Lookahead), the bytes can be a sequence of paragraphs with each paragraph containing a sequence of words. Each word will be a sequence of Unicode code points. The table below lists the action to take for each combination of the current class and the lookahead class. For a combination not present in the table, just advance to the next byte without taking any other action. 

Current /th Lookahead /th Action /th /tr
LF /td space /td Keep LF as current /td /tr
LF /td LF /td End of paragraph. The words since the last form the contents of the paragraph. Empty paragraphs are removed. /td /tr
other /td other /td part of word /td /tr
other /td not other /td end of word /td /tr
Kstandalone /td any /td if current is. or: and the Lookahead is space then the word of the current followed by the space is formed.Otherwise, the word of the current is formed. /td /tr
/table

PEG grammars /h3

We will be us in Parsing Expression Grammar (PEG) to describe the syntax of Tau. See Wikipedia for an introduction to PEG. We are using a similar syntax to that of Wikipedia, but will not include the operators: ? and &. Also, * is moved from the right side to the left side of the rule and parentheses are not meta characters. Here is how strings with balance parentheses would be represented: 

/td /tr
Start /td ← (N) /td /tr
* N /td ← Start /td /tr
/td / ! (!) any /td /tr
/table

The non-terminals are Start /em, N /em, any /em. The non-terminal, any /em, will match any terminal. The terminals explicitly used are the open and close parentheses. The terminal alphabet could be much larger. 

Structure of Tau source file /h3

Here is a PEG grammar describing the structure of a Tau source file where // emptyline /em represents one or more blank lines: 

/td /tr
* Modules /td ← Module ModName // emptyline /em Body /td /tr
/td / Module ModName.T // emptyline /em Body /td /tr
/td / module ModName // emptyline /em Body /td /tr
/td / module ModName.T // emptyline /em Body /td /tr
* Body /td ← Function FName Words // emptyline /em /td /tr
/td / function FName Words // emptyline /em /td /tr
/td / use ModName // emptyline /em /td /tr
/td / use ModName.Type // emptyline /em /td /tr
/td / Export type:Type Words // emptyline /em /td /tr
/td / Export Fname Words // emptyline /em /td /tr
/td / type TypeName is Words // emptyline /em /td /tr
/td / Builtin Words // emptyline /em /td /tr
/td / builtin Words // emptyline /em /td /tr
/td / unbound Words // emptyline /em /td /tr
/td / ! Module Words // emptyline /em /td /tr
* Words /td ← any /td /tr
Type /td ← TypeName.Type / int / real / word / boolean / TypeName /td /tr
ModName /td ← Id /td /tr
FuncName /td ← Id /td /tr
TypeName /td ← Id /td /tr
Id /td ← !, !] !) !:!.! dq any /td /tr
/table

Any text matching the" / ! Module Words" rule above is treated as a comment and can be omitted without changing the semantics. This will be any paragraph not beginning with one of the following words: Module, module, Function, function, use, Export, type, Builtin, builtin, unbound. This grammar does not specify the detailed syntax of paragraphs. 

Each module defines a set of functions and types. Paragraphs beginning with Function, function, and type declare functions and types. Only functions and types that are exported can be used outside of a module. The Export clause will export a function or type. If the F in the function definition is capitalized, it will be exported. 

The use clause determines which functions from other modules are available. 

The module standard /em defines often-used functions and types. A full list of functions is in this document itself, which can be fed directly to a Tau compiler. In this document, modules with names ending in a question mark, like in the next paragraph, are introduced solely for the purpose of allowing this document to compile. The following paragraphs define a module that exports some functions and types from the module standard. 

Module standard?

This module re-exports some common functions from the module standard. The use paragraph below makes visible in the module standard?, the functions and types in the module standard. The type int /em is always visible and cannot be exported. 

use standard

Export type:boolean

Export true boolean

Export false boolean

Export ∧(boolean, boolean) boolean
{The second operatand is evaluated if and only if the first operatand does not determine the result}

Export ∨(boolean, boolean) boolean
{The second operatand is evaluated if and only if the first operatand does not determine the result}

Export +(int, int) int {this exports the infix operator+}

Export type:word

Export type:seq.int

Export type:seq.word

Export type:ordering {For working with total orderings}

Export LT ordering

Export EQ ordering

Export GT ordering

Function >1(a:int, b:int) ordering if a > b then GT else if a = b then EQ else LT

Export ∧(a:ordering, b:ordering) ordering {if a = EQ then b else a}

Export %(n:int) seq.word
{By convention functions that begin with a % and have a return type of seq.word, supply a human-readable representation of its last argument.}

Export %(w:word) seq.word

Converting words to UTF8 /h3

A sequence of tau words must be converted back to UTF-8 to communicate with the outside world. When a file is read, whitespace is stripped, and it must be added back. 

The basic rules for adding spaces is to add a space after each word except when:

If the word is+-.. : then the space before and after the word is suppressed. /li

If the word is)]},  then the space before the word is suppressed. /li

If the word is ([{then the space after the word is suppressed. " /li /ul

There is a set of additional commands that provide additional formatting. Examples are given in the table below. 

Example /th with format /th note /th /tr
/td /tr
first //p second /td first //p second /td paragraph break /td /tr
first //br second /td first //br second /td line break /td /tr
* ///keyword example * /td *example * /td removes space before and after word./td /tr
///keyword <hr> /td<hr> /td ///keyword also does not escape < & in <hr> for html output./td /tr
a ///keyword" b" c /td a" b" c /td spacing around quotes /td /tr
/keyword/rmbr /td/tag &#32; /keyword/td/br /cell/td Toggles whether to interpret commands./td /tr
/table

The above rules are represented by the grammar below. The non-terminal N /em indicates that there is no pending space following the word.and S /em indicates that a space is pending. 

/td /td Action /td /tr
N /td ← S BA /td Do not add pending space to S /td /tr
/td ← S A /td Add pending space to S /td /tr
/td ← BA /td /tr
/td ← A /td /tr
+S /td B /td Do not add pending space /td /tr
/td ← ! BA ! A any /td Add pending space /td /tr
A /td ← (/ [/ {/td suppress space (A) fter /td /tr
B /td ←) /] /} /, /" /" /td suppress space (B) efore /td /tr
BA /td ←+/-/./. /:/: /td suppress space (B) before and (A) fter /td /tr
/table

There are a set of commands that alter these rules

CN /td ← NSBA /td /td /tr
/td ← // /em /td if last char is not space add one./td /tr
/td ← ///em ! / escapeformat any /td /td /tr
/td ← / br /td add a line break./td /tr
/td ← // /em /td add a paragraph break./td /tr
/td ← ec N /td /td /tr
/td ← CS NSBA /td /td /tr
/td ← CS A /td /td /tr
/td ← CS /td /td /tr
/td ← NSBA /td /td /tr
/td ← A /td /td /tr
+CS /td ← NSB /td /td /tr
/td ← // /em /td /td /tr
← ! BA ! B! ! /strong ! /em ! /br
! ec !any/td /tr
/table

Line breaks are handled by inserting formatting words. The simplest formatting rules are  /br for a line break and  /p for a paragraph break. 

An opening quote mark should be treated differently than a closing quote mark and the ASCII character set does not distinguish between opening and closing quote marks. Adding // /em will force a space after a word and will /em suppress the space before and after the next word. The spacing around an open quote mark can be expressed as // /em" /em to get" firstWord without the space after the quote mark. 

The format words are interpreted differently when producing plain text or HTML. For example, produces LF LF for plain text and <p> for HTML. Different functions are provided to do this. When creating output files from seq.word, if the file extension is HTML, the output is HTML; otherwise, plain text. 

Expressions /h2

We would like an expression such as a+3 * b sup 2 sup-2 to be evaluated to what a mathematician would expect. Adding parentheses specifies the order of evaluation: a+(3 * ((b sup (2 sup-2)). The binary operators+and * are left associative, and sup is right associative. The following is a PEG grammar for simple expressions. The order of evaluation is obscured by this grammar since left recursion must be eliminated. The left associative of+and * are taken care of in further processing, but the grammar takes care of the right associative nature of sup. 

/td /tr
E /td ← Sum /td /tr
Sum /td ← Product Sum' /td /tr
* Sum' /td ←-Product /+Product /td /tr
Product /td ← Unary Product' /td /tr
* Product' /td ← * Unary /td /tr
Unary /td ←-Unary / Power /td /tr
Power /td ← Atom Power' /td /tr
* Power' /td ←sub Unary / sup Unary /td /tr
Atom /td ← (E) / Id /td /tr
Id /td ← !, !) !:!.! dq any /td /tr
/table

Tau has many more binary operators than the above grammar handles. Below is the full list. Operators on the same line are of the same precedence. 

sup sub /br
unary minus /br
* / mod ∪ ∩ \ /br
+-∈ ∉ /br
= < > >1 >2 ≤ ≥ ≠ >> << /br
∧ /br
∨ ⊻ /br


Note that the operators ∪, ∩, and \ used for set union, intersection, and difference all share the same precedence. Here is the syntax for a procedure call and an if expression:

/td /tr
Unary /td ←-Unary / Id.Unary / Power /td /tr
Atom /td ← (E) /td /tr
/td / if E then E IF else E /td /tr
/td / Name (EL) /td /tr
/td / Name /td /tr
Name /td ← Id /td /tr
EL /td ← E EL' /td /tr
* EL' /td ←, E /td /tr
* IF /td ← else if E then E /td /tr
/table

A function call with a single argument can be expressed in one of two ways: // f1.a or f1 (a) /block. This allows expressions to be written with fewer parentheses. Note how the order of evaluation differs in the following expression: // not (a ∧ b) ≠ (not.a ∧ b) /block

The operators ≤ ≥ ≠ are syntactical abbreviations for not (a > b), not (a < b), not (a = b), respectively. 

Declaring Funcions/h2

Here are examples of two function definitions:

function quadratic(a:int, b:int, c:int, x:int) int a + b * x + c * x sup 2

Function quadratic(a:real, b:real, c:real, x:real) real a + b * x + c * x sup 2

The following paragraph is needed for the second function to compile:

use real

If two functions differ in name, number of parameters, or types of the parameters, they are considered distinct functions. Capitalizing the first letter of a Function implies the function is exported from the module. If the first letter is lowercase, the function is not exported unless an Export clause for the function is included, like:

Export quadratic(a:int, b:int, c:int, x:int) int

Here is the syntax for function definitions. It includes a non-terminal, Declare /em, which we define later. 

/td /tr
S /td ← function Name (FPL) Type Declare' E /td /tr
/td / function Name Type Declare' E /td /tr
/td / Function Name (FPL) Type Declare' E /td /tr
/td / Function Name Type Declare' E /td /tr
FPL /td ← FP FPL' /td /tr
* FPL' /td ←, FP /td /tr
FP /td ← any:Type / Type /td /tr
* Declare' Declare /td /tr
/table

A expression can always be viewed as a series of function calls. For the first function defined above, the values of the parameters can be viewed as the functions with no parameters with the function name being the parameter name and the function result type being the parameter type. 

The value of the integer literal 2 can be viewed as the function

Function 2 int 2

The infix binary operators are the functions that are defined in the Module standard

Export +(int, int) int

Export *(int, int) int

Export sup(int, int) int

Any expression has exactly one type that can be determined from the subexpression using the return type of the functions called. 

When calling a function, the types of the actual arguments MUST match the types specified in the function's definition. 

When defining a function, the type of the expression must match the return type of the function. 

Literals /h2

Below is a grammar that shows how characters are combined to form three types of literals with the names int /em, bits /em and real /em. Examples of int are 0 1 1000 1234. Exampes of bits are 0x1 0x0000 0X0a 0X0B. Examples of real are 0.0 1.0 1000.0 and 1234.456. Unlike most other PEG grammars in this document the grammar below has an alphabet of characters rather than words. 

/td /tr
Digit /td ← 0 / 1 / 2 / 3 / 4 / 5 / 6 / 7 / 8 / 9 /td /tr
* Digit' /td ← Digit /td /tr
int /td ← Digit' /td /tr
HexDigit /td ← Digit / A / B / C / D / E / F / a / b / c / d / e / f /td /tr
* HexDigit' /td ← HexDigit /td /tr
bits /td ← 0 X Digit Digit' / 0 x Digit Digit' /td /tr
real /td ← Digit Digit'.Digit Digit' /td /tr
/table

Strings in Tau are defined as a sequence of words (seq.word). An example literal for a sequence of words is" this is a sample string of 8 words" A simple grammar for strings would be // String ←" Str2" * Str2 ← !" any /block

But Tau allows a string to include an expression of type seq /em.word. The example literal above could also be represented as" this is a:(" sample string") of 8 words" So the grammar becomes

String /td ← /td" String' Str2" /td /tr
* String' /td ← /td:(E) /td /tr
/td / /td Str2 /td /tr
+Str2 /td ← /td !" !:any /td /tr
/table

There are two functions named dq /em in the standard package. The first takes no arguments and returns the sequence of one word consisting of a single doublequote character. The second function takes a sequence of words as an argument and returns the args with a double quote added to the beginning and end. 

These function allow a double quote within a string. For example: //" hello world without quotes;:(dq) hello world:(dq) with quotes" /block is the same as writing //" hello world without quotes;"+dq+" hello world"+dq+" with quotes" /block Since:(...) can receive any expression we could also write" hello world without quotes:(dq." hello world") with quotes" Since":(" functions as an escape in strings, it can be include within a string as":(":") (" Note that just the /: is escaped as":(":(")" will raise an error because the escape in the inner qoute is not properly formed. 

Declarations /h2

This section explains the constructs used in the following function:

Function exampeDeclarations int
let a = 33
{comment as declaration {nested comment}}
let b = 444
for sum = 0, product = 1, e ∈ "1 2 3 4 mark 5 6"
while e ∉ "mark"
do next(sum + toint.e, product * {comment within expression} toint.e)
assert product = 24 ∧ b = 444 report "Problem occured. Expect 24 but got:(product)",
sum + product

/td /tr
Declare /td ← let any = E comma? /td /tr
/td / assert E report E comma? /td /tr
/td / Comment comma? /td /tr
/td / for Accum AccumList', any ∈ E do E comma? /td /tr
/td / for Accum AccumList', any ∈ E while E do E comma? /td /tr
/td / for Accum AccumList' while E do E comma? /td /tr
* AccumList' cell ←, Accum /td /tr
Accum /td ← any = E /td /tr
Comment /td ← {N} /td /tr
* N /td ← Comment / str1 /td /tr
comma? ←, / /td /tr
/table

A let declaration in a function allows an name to be given to the value of an expression so the name references the value in the following expressions. A let statement DOES NOT define a variable that can change values. 

Comments are enclosed in curly brackets:{} and can be nested. Comments are traditionally defined at the lexical level. In tau, they are treated as prefix operators so they can be easily included in a parse tree. Comments can appear as declarations or as unary operators within expressions. 

The assert construct evaluates the first expression, which must be of type boolean. If the first expression is false, the second expression is evaluated and must be of type seq.word. The value of the second expression is thrown, and the evaluation of the function stops. If the first expression evaluates to true, execution continues as if the assert was omitted from the function. 

In the for construct in exampleDeclaration, sum and product are accumulators. Each accummulator is given an initial value. For each value e in the sequence, new values are calculated for each accumlator by the pseudo function next which also advances to the next value in the sequence if they are any. If a while expression is present it's type must be boolean, and is evaluated just after e is assign a value. If it is false the evaluation of the for construct is stopped. 

The sequence can be omitted from a for construct but then a while expression is required. 

Only the values of the accumlators are available outside the for construct.In the exampleDeclaration the identifiers sum product and e will take on the values

/td /tr
sum /strong /td product /strong /td e /strong /td /tr
0 /td 1 /td 1 /td /tr
1 /td 1 /td 2 /td /tr
3 /td 2 /td 3 /td /tr
6 /td 6 /td 4 /td /tr
10 /td 24 /td undefined /td /tr
/table

If only one accumulation is declared then the next function can be dropped, for example:

function sum(s:seq.int) int
for accumulator = 0, e ∈ s do accumulator + e,
accumulator

The optional comma in declarations can usually be left out, but there are exceptions. In the following function the comma cannot be left out or a error will occur as

Function neccessaryComma int
let b = 1,
-b

Sequences /h2

A sequence is a function whose domain is the integers and whose range is some type. A literal for a sequence of integers is coded as [2, 4, 8, 16, 32] and has a type of seq.type. 

A sequence of characters in double quotes does not represent a sequence of characters but a sequence of words. “Hello World!” represent two words. 

Sequences have the following functions defined in a parameteized module named seq.T where T can be any type. 

Module seq?.T

use seq.T

Export n(seq.T) int {the length of the sequence.}

Export sub(a:seq.T, i:int) T
{Return ith element of sequence. a sub 1 is the first element}

Export empty:seq.T seq.T {Returns the sequence of type seq.T with zero elements}

Export +(a:seq.T, b:seq.T) seq.T {Concatenation operator}

Export subseq(s:seq.T, start:int, stop:int) seq.T {Obtain sub-sequence}

Export =(a:seq.T, b:seq.T) boolean
{Test to see if a and b represent the same sequence.This function requires a function = (T, T) boolean}

The module standard exports the above functions with T replace by the type word

The function below is an example of using these functions. 

Module testseq

use standard

Function testseq seq.word
let s1 = "This is a test sequence with 9 words.",
if n.s1 = 9
∧ s1 sub 3 = "a" sub 1
∧ s1 sub n.s1 = 'words
∧ subseq(s1, 4, 5) = "test sequence"
∧ subseq(s1, 4, 3) = empty:seq.word
∧ subseq(s1, 1, 5) + subseq(s1, 6, n.s1) = s1
∧ ["Hello" sub 1, "World!" sub 1] = "Hello World!"
∧ empty:seq.word = ""
∧ subseq([11, 12, 13, 14], 1, 2) = [11, 12] then "PASS"
else "FAIL"

User Types /h2

The module below defines a user defined type. 

Module point2d

The follow paragraph that begins with use allows reference to functions defined in another module. In this case, the standard library functions. 

use standard

Here is a simple type definition that introduces a new type with two components and supplies functions to create a point2d and access its components. 

type point2d is x:int, y:int

To allow the type name to be used outside this module we export the type using a special syntax that omits the return type of the Export:

Export type:point2d

To allow the constructor for points to be used outside the module we export it:

Export point2d(a:int, b:int) point2d

Access to the fields outside the module is granted with:

Export x(point2d) int

Export y(point2d) int

The following two paragraphs defines an addition and subtraction function on the type point2d. If a function starts with function instead of Function the function is also not available outside the module. 

Function +(a:point2d, b:point2d) point2d point2d(x.a + x.b, y.a + y.b)

Function -(a:point2d, b:point2d) point2d point2d(x.a - x.b, y.a - y.b)

Function %(p:point2d) seq.word "(:(x.p),:(y.p))"

Function testpoint seq.word %(point2d(2, 3) + point2d(4, 5))

Module to run tests in this document /h2

Module testdoc

use standard

use file

use testseq

use point2d

use testlistset

use testdict

use exampleEncoding

use geotest

Function testdoc(input:seq.file) seq.word
{COMMAND}
" testseq:(testseq) point2d:(testpoint) testlistset:(testlistset) testdict:(testdict) exampleEncoding:(testExampleEncoding) geotest:(geotest)"

Parameterized Module /h2

A type can have a single type parameter named T. The T can be used anywhere a type can be used. 

Generic unbound functions on the type T may be included by using the word unbound as the defining expression. When the parameterized type is used, there must exist a function with the same signature as the unbound one, where T is replaced with the actual type for T. 

The following defines a parameterized set implemented as a sequence

Module listset.T

use standard

use seq.T

unbound =(T, T) boolean

type listset is toseq:seq.T

Export type:listset.T

Export toseq(s:listset.T) seq.T

Function empty:listset.T listset.T listset.empty:seq.T

Function ∈(ele:T, s:listset.T) boolean ele ∈ toseq.s

Function +(s:listset.T, ele:T) listset.T
if ele ∈ s then s else listset([ele] + toseq.s)

Function tolistset(s:seq.T) listset.T
{construct a listset from a sequence.(The compiler does not generate any code for this function since it is just a type change)}
for acc = empty:listset.T, ele ∈ s do acc + ele,
acc

Function ∪(a:listset.T, b:listset.T) listset.T
{This union is constructed so if an element is in both a and b, the representation in a is used in the result}
for acc = a, ele ∈ toseq.b do acc + ele,
acc

Export isempty(seq.T) boolean

Export sub(seq.T, int) T

Function lookup(s:listset.T, ele:T) seq.T lookup(toseq.s, ele)

The purpose of the last three function of the above module will become clear below. 

Module testlistset

use standard

use listset.word

Function testlistset seq.word
let set1 = tolistset."A A B C A C B"
let set2 = tolistset."D B E",
if toseq.set1 = "C B A" ∧ "C" sub 1 ∈ set1 ∧ "D" sub 1 ∉ set1 ∧ toseq(set1 ∪ set2) = "D E C B A" then "PASS"
else "FAIL"

Sets can be used to implement dictionaries. A dictionary contains entries. Each entry contains a key and a data component. A type is declared to represent an entry. In this example, the key will be an integer, and the data will be a sequence of words. Entries will be equal if and only if the keys are equal. 

type myentry is key:int, data:seq.word

function =(a:myentry, b:myentry) boolean key.a = key.b

A set of entries will be a dictionary. From the mathematical view of the set, each entry is a representation of an integer. The integer 3 could be represented by myentry (3," X"), myentry (3," A B C") or an infinite number of other possibilities. But only one representation will be used in any listset.myentry. 

Looking up an entry in the dictionary is just looking up the representation used in the set. The last function in the listset /em module does just that. The A ∪ B function in the listset module is carefully crafted so that if an element is in both A and B, the representation used in A is used in the result. Thus listset.[myentry (3," X")] ∪ B will redefine the entry in B if it exists. The expression B+myentry (3," X") or B ∪ [myentry (3," X")] will not redefine the entry in B. By convention, the result of a binary operation on sets uses the representation of in the left operand--not the one on the right. 

Module testdict

use standard

use seq.myentry

use listset.myentry

type myentry is key:int, data:seq.word

function =(a:myentry, b:myentry) boolean key.a = key.b

function lookup(a:listset.myentry, i:int) seq.myentry lookup(a, myentry(i, ""))

function print(a:listset.myentry) seq.word
for txt = "", ele ∈ toseq.a
do txt + "(" + toword.key.ele + "," + data.ele + "),",
txt >> 1

Function testdict seq.word
let dict = tolistset.[myentry(1, "add"), myentry(2, "sub"), myentry(3, "mult")]
let dict2 = tolistset.[myentry(2, "subtract"), myentry(4, "divide")]
let l1 = lookup(dict, 4),
if print.dict = "(3, mult), (2, sub), (1, add)"
∧ print.dict2 = "(4, divide), (2, subtract)"
∧ isempty.lookup(dict, 4)
∧ data.lookup(dict, 2) sub 1 = "sub"
∧ print(dict2 ∪ dict) = "(1, add), (3, mult), (4, divide), (2, subtract)" then "PASS testdict"
else "FAIL testdict"

For the type listset.word, the unbound function = in the listset module is bound to the function = (word, word) in the standard module. For the type listset.myentry, then unbound = is bound to = (a:myentry, b:myentry) boolean

>>.T in Parameterized Module. /h2

When defining graphs consisting of nodes and edges, the nodes and edges may be of different types. For example, the nodes may be of type T and the edges have a label of type seq.word. 

Module edge.T

use standard

type edge is tail:T, head:T, label:seq.word

In the parameterized graph module in the Tau release, the parameter is itself a parameterized type representing the graph edge type. So, within the graph module, T represents the edge type, and >>.T references the node type. That is, >>.T references the parameter of the parameter of the graph module. 

The following function would also be needed in the edge module to be used by the graph module

Function arc(node:T) edge.T
{used by module graph.edge.T when looking up edges}
edge(node, node, "")

Export head(node:edge.T) T {used by module graph.edge.T}

Export tail(node:edge.T) T {used by module graph.edge.T}

Bindings /h2

Consider the following example code:

Module B

Function TWO int 2

Module A

use B

use standard

Function f1(p1:int) int
let l1 = p1 * TWO,
p1 * l1 - THREE

function THREE int 3

Parameters implicitly declare an access function. Example: function p1 int

Parameters are only visible in the expression that defines the body. For example, p1 is only visible in the body of f1. 

The names of functions are visible.

Functions from another module B are visible in module A, if they are declared using Function rather than function, or they are exported and the module A includes a paragraph use B. The function TWO is visible in module A and B. 

A word of all digits implicitly declares an access function: function 3 int

Let definitions are only visible within the second expression in the let statement. Let definitions declare an access function: function l1 <the type of the first expression of the let>. The definition itself returns the type of the second expression. 

A function call f1 (<exp1>, <exp2>,...) must match exactly one visible function defintion in name, number of parameters and types of the expressions of the arguments. 

The type of the expression that defines a function much match the return type of the function. 

Order of evaluation /h2

The arguments of a function are evaluated from left to right before the function is called. 

Not all arguments need to be evaluated. Consider i > 0 ∧ 300 / i < 10 where ∧ is defined as: // function ∧ (a:boolean, b:boolean) boolean if a then b else false /block The compiler will do inline expansion and the above expression becomes // if i > 0 then 300 / i < 10 else false /block If i = 0 then the expression 300 / i < 10 is never evaluated. 

This behavior is required for the ∧ operator on booleans. 

Encodings /h2

A type can be mapped to positive integers in an encoding. 

The parameterized module encoding /em.T defines the following functions for working with encodings. 

Module encode?.T

use encoding.T

Export encode(T) encoding.T {will return the encoding}

Export decode(encoding.T) T {will return the value that was encoded}

Export findencode(T) seq.T
{will return the empty sequence if the value has not been mapped or a sequence containing the value that was mapped.}

Export encodingdata:T seq.T {list of values that have been encoded.}

Export valueofencoding(encoding.T) int {the integer value of the encoding}

Since the encoding can be shared by multiple processes, modifying the encoding is a critical section. Also, the mapping may contain encodings not assigned by the current process. 

Encodings do not exist until a process references them; once referenced, the process owns the encoding. 

A child process shares any encodings that its parents' process has. 

A process does not share the encodings it owns with siblings or parents. 

Module exampleEncoding

This is an example use of an encoding that encodes sub-expression of a postfix expression and then produces code that evaluates any common sub-expressions only once. 

use standard

use seq.encoding.myencoding

use encoding.myencoding

use stack.encoding.myencoding

We need a type to encode:

type myencoding is op:word, operands:seq.encoding.myencoding

We must define a hash function and = function of the type myendcoding. 

function hash(m:myencoding) int hash.op.m

function =(a:myencoding, b:myencoding) boolean op.a = op.b ∧ operands.a = operands.b

Note that for a and b of the type myencoding, a = b implies hash (a) = hash (b). This must be true for the hash to work correctly. The hash function in this example could be improved by including operands in the argument. 

Function testExampleEncoding seq.word
let R = "R1 R2 R3 R4 R5 R6 R7 R8 R9 R11 R12 R13"
let postfix = "5 3 4+* 3 4+* 6 3 4+*+7+"
{encode every subexpression of the postfix expression. If a sub-expression is used more that once it will have the same encoding every time it is used. /rmbr/br Below a stack is used. The definition is in core.}
let encodingofpostfix =
 for stk = empty:stack.encoding.myencoding, w ∈ postfix
 do
  if w ∈ "+*" then push(pop.pop.stk, encode.myencoding(w, top(stk, 2)))
  else push(stk, encode.myencoding(w, empty:seq.encoding.myencoding)),
 top.stk
{all the encodings are now in encodingdata:myencoding. It is now easy to print out instruction that will evaluate common subexpressions only once}
for acc = "", idx = 1, e ∈ encodingdata:myencoding
do
 let newacc =
  acc
  + "/br"
  + R sub idx
  + "="
  + if op.e ∈ "+, *" then [R sub valueofencoding.(operands.e) sub 1, op.e, R sub valueofencoding.(operands.e) sub 2]
  else [op.e],
 next(newacc, idx + 1),
acc

The testexample output is: R1 = 5 /br
R2 = 3 /br
R3 = 4 /br
R4 = R2+R3 /br
R5 = R1 * R4 /br
R6 = R5 * R4 /br
R7 = 6 /br
R8 = R7 * R4 /br
R9 = R6+R8 /br
R11 = 7 /br
R12 = R9+R11

Consider the sequence of calls, C, in the execution of the program to the function encode. Let S be the sequence of T where S_i is the value passed as parameter in call C_i Let E be the sequence of results where E_i = the result of call C_i. 

Then S_i = S_j if and only if encoding (E_i) = encoding (E_j) and decode (E_i) is identical to S_j where j = min t where S_t = E_i and encoding (E_i) > 0

Process statement /h2

Processes are included in Tau for three reasons. 

Running multiple processes on multi-core processors can produce results more quickly. 

Processes allow temporary space used to calculate the result to be reclaimed. This is the only way for heap space to be reclaimed Processes allow temporary space used for calculations to be reclaimed. This is the only method for heap space to be reclaimed in Tau.in Tau. 

Processes capture and report abnormal events. The following code snippet shows how to capture an abnormal event. 

Module testprocess

use process.int

use standard

function myprocess(a:int) int
assert a > 0 report "invalid",
a sup 3

function useprocess(i:int) int
{Note that the result type of this function matches the parameter in the use clause above. This provides access to the pseudo-function process below and allows a spawned process of type process.int to be created from the function myprocess}
let a = process.myprocess.i,
if aborted.a then
 assert message.a = "invalid" report "new message",
 0
else result.a

The following functions interact with the spawned process and block to wait for the spawned process to finish. 

Module process?.T

use process.T

use standard

Export aborted(process.T) boolean
{true if the process was aborted as with an assert statement}

Export message(process.T) seq.word {message return when process was aborted}

Export result(process.T) T {result return upon successful completion. }

The spawning process cannot terminate until all of it child process complete, because it may have allocated space and passed it to a child process as a parameter. 

Defining Sequences /h2

Sometimes it is useful to define a new sequence type. Here we defined a geometric sequence moduled after the arithmetic seq define in seq1.T

Module geometricseq.T

All sequences must be in a parameterized Module. 

use standard

We need some operations on T. 

unbound *(T, T) T

unbound sup(T, int) T

type geometricseq is sequence, step:T, start:T

The above type is recognized as a sequence as the first element of the type is sequence. 

A function length /em (myseq) is implicitly defined to access the length of geometricseq

As with any parameterized module, a type definition must contain an element that uses T so that multiple instances of the module do not produce duplicate symbols. 

Every sequence must have a#function defined on it:

Function sequenceIndex(s:geometricseq.T, i:int) T start.s * (step.s) sup (i - 1)

We need a constructor of our sequence. Note the use of a toseq function. This is defined implicitly by the sequence type definition to change the type from geometricseq.T to seq.T

Function geoseq(length:int, step:T, start:T) seq.T
toseq.geometricseq(length, step, start)

Module geotest

use standard

use geometricseq.real

use geometricseq.int

use real

Function geotest seq.word
 "first 10 powers of 2 ="
 + %.geoseq(10, 2, 2)
 + "/br first 10 powers of 0.5 ="
 + %.geoseq(10, 0.5, 0.5)

The following are needed to define % (seq.int) and % (seq.real). 

use seq1.int

use seq1.real

Function %(a:real) seq.word %(10, a)

End of module geotest. 

Tail Recursion /h2

A function is tail-recursive if the last function called is itself. A compiler can take advantage of this and reuse the activation record on the call stack, reducing the space the stack consumes during execution. 

Sometimes a recursive function can be rewritten to be tail-recursive. Consider the following function:

use seq.int

function reverse2(l:seq.int) seq.int
if isempty.l then l else reverse2.subseq(l, 2, n.l) + l sub 1

The last call in this function is to+. Here is a rewritten version that is tail recursive:

function reverse3(l:seq.int, accumalator:seq.int) seq.int
if isempty.l then accumalator else reverse3(subseq(l, 2, n.l), accumalator + l sub 1)

function reverse3(l:seq.int) seq.int reverse3(l, empty:seq.int)

Now reverse3 is the last function called. 

Making the function tail-recursive is not the only way to reduce stack usage. The follow version uses O (ln n) instead of O (n) where n is the length of the sequence. 

function reverse4(l:seq.int) seq.int
if n.l < 2 then l
else reverse4.subseq(l, n.l / 2 + 1, n.l) + reverse4.subseq(l, 1, n.l / 2)

Perhaps the best way to reverse a sequence is to use

Function reverse5(s:seq.int) seq.int
for acc = empty:seq.int, e ∈ s do [e] + acc,
acc

In this case, the tau compiler will remove the bounds checking when indexing the sequence. If the sequence was built up out of smaller sequences, it may also break the sequence into the smaller parts and process them separately. 

END 