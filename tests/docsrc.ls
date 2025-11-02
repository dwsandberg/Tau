/tag <style><!--span.code1 { border:solid; border-width: thin;} 
 span.code { font-family:italic;}--> /tag </style> 
 

<* code this /tag <br> is a test *> 

/tag <h1> The Tau Programming Language  /tag </h1>

Programming languages today look pretty much the same as they did 30 years ago. Today they may have a few more features but are not substancally better as a notation for thought. I have created another programming language in attempt to introduce a new way to think about programming.

This new language is different because there is:
<* block —No assignment operator. /br —No loop/while statement 
/br —No function type./br —Only uses program state in a very controlled way. /br —Words are the basic text element instead of characters. 
/br —Heavy use of sequences. 
/br —Introduces a new control structure for iterating through loops.*>


Functional program languages have no assignment operator or loop statements, but tend to be based on the lamada calculus which makes use of higher order functions. We only include the basic operations on function of declaring and calling of them and the binding of unbound function to an actual function in an instantiation of a function from a parameterized module.

Functional languages tend to use recursion to replace the control structures of loops. 
The full power of recursion is seldom needed. 
We introduce a  new control structure  to cover many of the simple uses of recursion.

Instruction for downloading and install Tau in /tag <a /sp href="installdoc.html"> here 
/tag </a> /sp  if you would
like to try out the examples below for yourself.

/tag <h2> Basic Structure /tag </h2> 

Tau is word based rather than character based. A source file for Tau is a UTF-8 encoded file. 
   Blank lines in the file   breaking the
file into a sequence of paragraphs.  Spaces seperate words.
Some characters such as + form a word of a single character even when there
is no space before or after. Paragraphs are further group into \em modules. 

/tag <h3> Converting UTF-8 to a sequence of paragraphs /tag </h3> 

Tau transforms the bytes of the UTF-8 encoded file into a sequence of paragraphs by classify the bytes into 5 groups.
<* block
/br The LF group is the ASCII linefeed character.
/br The Space group is the ASCII space and the carriage return. 
  The  carriage return is added 
  to handle the end of line representation in DOS.
/br The StandAlone group is the ASCII characters ()+,-..:=[]{} and the double quote.
/br The other group which contains any byte not included in the other three groups. 
*>
By considering the class of each byte(the current byte) and the next byte (the Lookahead)
the bytes can be a seqence of paragraphs with each paragraph containing a sequence of words. Each word will be a sequence of unicode code points. The table below contain the Action to take for each combination of the class of current and lookahead. For combination not present in the table just advance to the next byte without taking any other action.
  <* table
  /row /strong Current /cell /strong Lookahead /cell /strong Action
  /row  LF /cell  space /cell     Keep LF as current 
   /row   LF /cell LF  /cell  End of paragraph. The words since the last 
   form the contents of the paragraph.  Empty paragraphs are removed.
   /row   other   /cell other    /cell part of word
   /row  other   /cell   not    other   /cell end of word
   /row Kstandalone /cell any /cell 
     if current   is . or : and the Lookahead is space then
      the word of the current followed  by the space is formed.
     other the word of the current is formed. 
*>
    
/tag <h3> PEG grammars /tag </h3> 


We will be us in   Parsing Expression Grammar(PEG) to describe the syntax of Tau. 
See Wikipedia for an introduction to PEG.  We be using a similar syntax to that 
descibe in Wikipedia but  will not include the operators: ?  and  &. Also * is moved from
the right side to left side of the rule and parentheses are not meta characters.   Here is how strings with
balance parenthesis would be represented:
<* table
/row Start  /cell   ← ( N  )
/row * N    /cell ← Start 
/row /cell /  ! ( ! ) any 
*>
The non-terminals are /em Start, /em N, /em any. The non-terminal, /em any, will
match any termial.  The terminals explicitly used are the open and close 
paranethesis. The terminal alphabet could be much larger.

/tag <h3> Structure of Tau source file /tag </h3> 


Here is a PEG grammar describing the structure of a Tau source file
where /em /p represents one or more  blank lines:
<* table
/row * Modules /cell ←  Module ModName /em /p Body
/row /cell / Module ModName.T /em /p Body
/row /cell / module ModName  /em /p Body
/row /cell / module ModName.T /em /p Body
/row * Body  /cell ←  Function FName Words /em /p 
/row /cell / function FName Words /em /p
/row /cell / use ModName /em /p  
/row /cell / use ModName.Type /em /p
/row /cell / Export type:Type Words /em /p  
/row /cell / Export Fname Words /em /p
/row /cell / type TypeName is Words /em /p
/row /cell / Builtin Words /em /p 
/row /cell / builtin Words /em /p
/row /cell / unbound Words /em /p
/row /cell / ! Module Words /em /p
/row * Words /cell ← any
/row Type /cell ←  TypeName.Type / int / real / word / boolean / TypeName
/row ModName /cell ← Id
/row FuncName /cell ← Id
/row TypeName /cell ← Id
/row Id /cell ← !, !] !) !:!.! dq any
*>   

Any text matching the "/ ! Module Words " rule above is treated as a comment and can be omitted without changing the semantics.  This will be any paragraph not beginning with one of the following words: 
Module module Function function use Export type Builtin builtin unbound.  This grammar does not specifiy the detailed syntax of paragraphs.

Each module defines a set of functions and types.  Paragraphs beginning
with Function, function and type declare functions and types. 
 Only functions and types that are exported can be used outside of a module.  The Export clause will export a function or type. 
A function is also exported if the first letter of the paragraph defining
the function is capitalize. 

The use clause determines which functions from other modules are available. 

The module /em standard defines often used functions and types. 
 A full list of functions is /sp
/tag  <a /sp href ='./core.html#standard'>  here /tag </a>. 
Many of the functions are defined in other modules and only exported from the standard module. A few note worth types and functions are list below.

This document itself can be feed directly to a Tau compiler. In this document modules  with names ending in a question mark like in the next paragraph  are introduced solely for the purpose of allowing this document to compile. The following paragraphs define a  module  that exports some functions and types from the module standard. 

Module standard?

This modules re-exports some common function from the module standard. The use paragraph below makes visible in module standard? the function and types in the module standard.
The type /em int is always visible so cannot be exported but if it could be the paragraph would look like: <* block Export type:int *>

use standard

Export type:boolean

Export true boolean

Export false boolean

Export ∧(boolean, boolean) boolean
{The second operatand is evaluated if and only if the first operatand does not determine the result}

Export ∨(boolean, boolean) boolean
{The second operatand is evaluated if and only if the first operatand does not determine the result}

Export +(int,int) int { this exports the infix operator +}

Export type:word

Export type:seq.int

Export type:seq.word

Export type:ordering {For working with total orderings}

Export LT ordering

Export EQ ordering

Export GT ordering

Function >1(a:int, b:int) ordering if a > b then GT else if a = b then EQ else LT

Export ∧(a:ordering, b:ordering)ordering 
  { if a = EQ   then b   else a}

Export %(n:int) seq.word
{By convention function that begin with a % have a return type of seq.word, supply a human
 readable representation.}

Export %(w:word) seq.word

/tag <h3> Converting words to UTF8 /tag </h3>

A sequence of tau words must be transformed back to UTF8 format to communicate with the outside world. When a file is read the white space is striped out and must be added back in. 

The basic rules for adding spaces is to add a space after each word except when:
/br 1. If the word is /sp+-.. :/sp then the space before and after the word is suppressed. 
/br 2. If the word is /sp)]}," then the space before the word is suppressed.
/br 3. If the word is ([{then the space after the word is suppressed. "

There are a set of addition commands that provide additional formatting.  Examples are given in the table below. 
 
<* table /tag <caption> Markup Commands
/tag <tr><th> Example /tag  <th>  with format /tag  <th> note
/row first /keyword
/p second /cell first
/p second /cell paragraph break
/row first /keyword
/br second /cell first
/br second /cell line break
/row /keyword /em example /cell /em example /cell
/row /keyword /strong example /cell /strong example /cell
/row /keyword /keyword example /cell /keyword example /cell
/row /keyword <* /keyword literal this is an example /keyword *> /cell <* literal this is an example *> /cell
/row /keyword <* /keyword keyword this is an example /keyword *> /cell <* keyword this is an example *> /cell
/row /keyword <* /keyword comment this is an example /keyword *> /cell <* comment this is an example *> /cell
/row parent
/br block /keyword <* /keyword block Indented block. 
/br /keyword
/br second line /keyword *> /cell parent block <* block Indented block. 
/br second line *> /cell Indented block
/row +/keyword /sp+ /cell  +/sp+/cell  add space after last word
/row +/keyword /sp /keyword /sp+ /cell  +/sp /sp+ /cell only adds space not already there.
/row * /keyword /tag example * /cell  * /tag  example *   /cell removes space before and after word.
/row /keyword /tag <hr>   /cell /tag <hr> /cell /keyword /tag also does not escape < &
in <hr> for html output.
/row  a /keyword /sp /keyword /tag "b" c /cell a   /sp   /tag "b" c /cell spacing around quotes
/row  /keyword <* /keyword table   <rows of table> /keyword *> /cell /cell Defines a table
/row../keyword /cell../keyword /cell.. /cell /cell Defines a row with three columns. 
/br Must be placed within table. 
/row /keyword <* /keyword table  
/br /keyword
/row 1 /keyword /cell 2 /keyword /cell 3
/br /keyword
/row 3 /keyword /cell 4 /keyword /cell 5 /keyword *> /cell <* table  
/row 1 /cell 2 /cell 3
/row 3 /cell 4 /cell 5 *> /cell 
/row /keyword /escapeformat /escapeformat /br /cell /escapeformat /tag &#32; /keyword /escapeformat /cell /escapeformat  /br /cell /escapeformat  /cell
Toggles whether to interpret commands.
*>

The above rules are represented by the grammar below. 
The non-terminal /em N represents no following space the word is pending
and /em S represents there is a space pending. 


<* table 
   /row /cell /cell Action
   /row N   /cell  ← S BA  /cell Do not add pending space to S
  /row    /cell  ← S A /cell Add pending space to S
  /row    /cell  ←   BA 
  /row   /cell  ←  A 
  /row   + S /cell B  /cell Do not add pending space
  /row /cell ← ! BA ! A  any /cell Add pending space
    /row  A  /cell  ← ( /[ /{ /cell suppress space (A)fter 
  /row  B  /cell ←  ) /] /} / , / " /"/cell suppress space (B)efore 
  /row  BA /cell ← + /-  /./. / :/:   /cell suppress space (B) before and (A)fter
*>

There are a set of commands that alter these rules 

<* table 
 /row CN /cell  ← NSBA /cell    
 /row /cell  ← /em /sp /cell   if last char is not space add one.
 /row /cell  ← /em /tag ! /sp /tag / escapeformat  /sp any /cell   
 /row /cell  ←  /sp /tag / br /cell   add a line break.
 /row /cell  ← /em /p /cell   add a paragraph break.
 /row /cell  ← /em <* /em block CN /em  *>  
 /row /cell  ← /em <* /em table CN /em  *> 
   /row /cell  ← ec N /cell    
 /row /cell  ← CS NSBA /cell    
 /row /cell  ← CS A /cell    
 /row /cell  ← CS /cell    
 /row /cell  ← NSBA /cell   
 /row /cell  ← A /cell   
 /row +CS /cell  ← NSB /cell   
 /row /cell  ← /em /keyword any
 /row /cell  ← /em /em any
 /row /cell  ← /em /strong any
   /row /cell  ←  /em /cell  /cell    
 /row /cell  ← /em /row /cell    
 /row /cell  ←  /em <* ! block ! table any CN /em *>
 /row /cell  ←  /em  /sp 
  /row /cell  ← ! BA ! B /escapeformat !
 /p ! /strong ! /em ! /br ! <* ! *> ! ec ! /tag any /escapeformat *>


Line breaks are handled by inserting formatting words. The simplest formatting rules are  /br for a
line break and  /p for a paragraph break. 

An opening quote mark should be treated differently than a closing quote mark and the ASCII character
set does not distinguish between opening and closing quote marks. Adding /em /sp will force a space after a word and /em /tag will suppress the space before and after the next word. The spacing around a open qoute mark can be expressed as /em /sp /em /tag " to get /sp /tag " firstWord without the space after the quote mark. 
 

The format words are interpreted differently when producing plain text or HTML. For example, /keyword
/p produces LF LF for plain text and   <p>  for HTML. Different functions are provide to do this. When creating files from seq.word for output, if file extension is html then the output is HTML otherwise plain text.

/tag <h2>   Expressions /tag </h2>

We would like an expression such as a+3 * b sup 2 sup -2 to evaluation to what a mathematician would expect. Adding parenthesis specifies the order of evaluation: a+(3 * (
(b sup (2 sup -2)). The binary operators /sp+/sp and * are left associative and /sp sup /sp is right associative
.

The following is a PEG grammar for simple expressions. The order of evaluation is obscured by this
grammar since left recursion must be elimiated. The left associative of+and * are taken care of
in further processing, but the grammar takes care of the right associative nature of sup . <* table
/row E /cell ← Sum
/row Sum /cell ← Product Sum'
/row * Sum' /cell ←-Product /+Product
/row Product /cell ← Unary Product'
/row * Product' /cell ← * Unary
/row Unary /cell ←-Unary / Power
/row Power /cell ← Atom Power'
/row * Power' /cell ←sub Unary / sup Unary
/row Atom /cell ← (E) / Id
/row Id /cell ← !, !) !:!.! dq any *>

Tau has many more binary operators than the above grammar handles. Below is the full list. Operators
on the same line are of the same precedence. <* block
/br sup sub
/br unary minus
/br * / mod ∪ ∩ \
/br+-∈ ∉
/br = < > >1 >2 ≤ ≥ ≠ >> <<
/br ∧
/br ∨ ⊻ *>

Note that the operators ∪ ∩ \ which are commonly used for set union, intersection and differences all
have that same precedence.

Here is the syntax for a procedure call and if expression: <* table
/row Unary /cell ←-Unary / Id.Unary / Power
/row Atom /cell ← (E)
/row /cell / if E then E IF else E
/row /cell / Name (EL)
/row /cell / Name
/row Name /cell ← Id
/row EL /cell ← E EL'
/row * EL' /cell ←, E
/row * IF /cell ← else if E then E *>

A function call with a single argument can be expressed one of two ways: <* block f1.a *> or <* block f1 /tag(a) *> This allows expressions
to be written with fewer parentheses. Note how the order of evaluation differs in the following expression
:<* block not (a ∧ b) ≠ (not.a ∧ b) *>

The operators ≤ ≥ ≠ are syntatical abbreviations for not /tag (a > b), not /tag (a < b), not /tag (a = b) respectively. 

/tag <h2> Function Declarations /tag </h2>

Here are exampls of two function definitions:

function quadratic(a:int, b:int, c:int, x:int) int a + b * x + c * x sup 2

Function quadratic(a:real, b:real, c:real, x:real) real a + b * x + c * x sup 2

The follow paragraph is need for the second function to compile:

use real

If two function differ in name, number of parameters, or types of the parmeters they are consider distinct functions. Capatilizing the first letter of Function implies the function is Export from the module. If the first letter is lower case the function is not exported unless an Export clause for the function is include like:

Export quadratic(a:int, b:int, c:int, x:int) int

Here is the syntax for function definitions. It includes a non-terminal, /em Declare, which we define later.

<* table
/row S /cell ← function Name (FPL) Type Declare' E
/row /cell / function Name Type Declare' E
/row /cell / Function Name (FPL) Type Declare' E
/row /cell / Function Name Type Declare' E
/row FPL /cell ← FP FPL'
/row * FPL' /cell ←, FP
/row FP /cell ← any:Type / Type
/row * Declare' Declare *>

A expression can always be viewed as a series of function calls. For the first function defined above
the values of the parameters can be viewed as the functions with no parameters with the function name
being the parameter name and the function result type being the parameter type.

The value of the integer literal 2 can be view as the function 

Function 2 int 2

The infix binary operators are the functions which are defined in the Module standard

Export +(int, int) int

Export *(int, int) int

Export sup(int, int) int

Any expression has excatly one type that can be determine from the subexpression using the return type
of the functions called. 

When calling a function the types of actual arguments MUST match the types given in the definition of the function. 

When defining a function the type of the expression must match the return type of the function. 

/tag <h2> Literals /tag </h2>

Below is a grammar than shows how characters are combined to form three types of literals with the names
/em int, /em bits and /em real. Examples of int are 0 1 1000 1234. Exampes of bits are 0x1 0x0000 0X0a 0X0B. Examples of real are 0.0 1.0 1000.0 and 1234.456.  Unlike most other PEG grammars in this document the grammar below has an alphabet of characters rather than words.

<* table
/row Digit /cell ← 0 / 1 / 2 / 3 / 4 / 5 / 6 / 7 / 8 / 9
/row * Digit' /cell ← Digit
/row int /cell ← Digit'
/row HexDigit /cell ← Digit / A / B / C / D / E / F / a / b / c / d / e / f
/row * HexDigit' /cell ← HexDigit
/row bits /cell ← 0 X Digit Digit' / 0 x Digit Digit'
/row real /cell ← Digit Digit'.Digit Digit' *>

String in Tau are defined as a sequence of words (seq.word). An example literal for a sequence of words
is /sp /tag " this is a sample string of 8 words" A simple grammar for strings would be <* block
 String ←" Str2"
/br * Str2 ← !" any *> But Tau   allows a string to include an expression of type /em seq.word. The
example literal above could also be represented as" this is a:(" sample string") of 8 words" So
the grammar becomes <* table
/row String /cell ← /cell" String' Str2"
/row * String' /cell ← /cell :(E)
/row /cell / /cell Str2
/row + Str2 /cell ← /cell !" !:any *>

There are two function named /em dq in the stardard package. The first that takes no arguments and returns the sequence of words with one word consisting of single doublequote character. The second function takes a sequence of words as an argument and returns the args with a doublequote added to the begining and end. 

These function allow a double quote within a string. For example:
<* block /tag " hello world without quotes;
:(dq) hello world:(dq) with quotes" *> is the same as writing 
<* block /tag " hello world without quotes;" /sp+/sp dq
/sp+/sp /tag " hello world"+/sp dq /sp+/sp /tag "   with quotes" *> Since:(...) can receive any expression we could also write
<* block   /tag "   hello world without quotes:(dq./tag " hello world") with quotes" *> Since  /sp /tag ":(" functions as an escape in
strings, it can be include within a string as /sp /tag":(/tag":") (" Note that just the / /sp : /sp is escaped as
/sp":( /tag " :(")" will raise an error because the escape in the inner qoute is not properly formed.

/tag <h2> Declarations /tag </h2>

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

Here is the grammar for constructs used in this section: <* table
/row Declare /cell ← let any = E comma?
/row /cell / assert E report E comma?
/row /cell / Comment comma?
/row /cell / for Accum AccumList', any ∈ E do E comma?
/row /cell / for Accum AccumList', any ∈ E while E do E comma?
/row /cell / for Accum AccumList' while E do E comma?
/row * AccumList' cell ←, Accum
/row Accum /cell ← any = E
/row Comment /cell ← {N}
/row * N /cell ← Comment / str1 
/row comma? ←, / *>

A /keyword let declaration in a function allows an name to be given to the value of an expression so the name
references the value in the following expressions. A let statement DOES NOT define a variable that can
change values.

Comments are enclosed in curly brackets:{} and can be nested. Comments are traditionally defined at the lexical level. In tau they are defined as a prefix operator so that they can easily be included in a parse tree. Comments can occur as a declaration or as a unary operator within expressions. 

The /keyword assert construct evaluates the first expression which must be of type boolean. If the first expression
is false the second expression is evaluated and must be of type seq.word. The value of the second exporess
is thrown and evaluation of the function stops. If the first expression evaluates to true execution continues
as if the assert was omitted from the function.

In the /keyword for construct in exampleDeclaration sum and product are accumlators. Each accummulator is given
an initial value. For each value e in the sequence, new values are calculated for each accumlator by
the pseudo function next which also advances to the next value in the sequence if they are any. If
a while expression is present it's type must be boolean, and is evaluated just after e is assign a value
. If it is false the evaluation of the for construct is stopped. 

The sequence can be omitted from a /keyword for construct but then a while expression is required.

Only the values of the accumlators are available outside the for construct.

In the exampleDeclaration the identifiers sum product and e will take on the values <* table
/row /strong sum /cell /strong product /cell /strong e
/row 0 /cell 1 /cell 1
/row 1 /cell 1 /cell 2
/row 3 /cell 2 /cell 3
/row 6 /cell 6 /cell 4
/row 10 /cell 24 /cell undefined *>

If only one accumulation is declared then the next function can be dropped, for example:

function sum(s:seq.int) int for accumulator = 0, e ∈ s do accumulator + e, accumulator

The optional comma in declarations can usually be left out, but there are exceptions. In the following
function the comma cannot be left out or a error will occur as

Function neccessaryComma int let b = 1,-b



/tag <h2> Sequences /tag </h2>

A sequence is a function whose domain is the integers and whose range is some type. A literal for a
sequence of integers is coded as <* code [2, 4, 8, 16, 32] *> and has a type of <* code seq.type *>. 

A sequence of characters in double quotes does not represent a sequence of characters but a sequence
of words. <* code “Hello World!” *> represent two words.

Sequences have the following functions defined in a parameteized module named <* code seq.T *> where T can be any
type.  

Module seq?.T

use seq.T

Export n(seq.T) int {the length of the sequence.}

Export sub( a:seq.T,i:int) T {Return ith element of sequence. a sub 1 is the first element}

Export empty:seq.T seq.T {Returns the sequence of type seq.T with zero elements}

Export +(a:seq.T, b:seq.T) seq.T {Concatenation operator}

Export subseq(s:seq.T, start:int, stop:int) seq.T {Obtain sub-sequence}

Export =(a:seq.T, b:seq.T) boolean
{Test to see if a and b represent the same sequence.This function requires a function = (T, T)
 boolean}

The module <* code standard *> exports the above functions with T replace by the type <* code word *>

The function below is an example of using these functions. 

Module testseq

use standard

Function testseq seq.word
let s1 = "This is a test sequence with 9 words.",
if
 n.s1 = 9
 ∧  s1 sub 3 =  "a" sub 1
 ∧  s1 sub n.s1 = 'words 
 ∧  subseq(s1, 4, 5) = "test sequence"
 ∧ subseq(s1, 4, 3) = empty:seq.word
 ∧ subseq(s1, 1, 5) + subseq(s1, 6, n.s1) = s1
 ∧ ["Hello" sub 1,  "World!" sub 1] = "Hello World!"
 ∧ empty:seq.word = ""
 ∧ subseq([11, 12, 13, 14], 1, 2) = [11, 12]
then
"PASS"
else "FAIL" 

/tag <h2> User Types /tag </h2>

The module below defines a user defined type. 

Module point2d

The follow paragraph that begins with /keyword use allows reference to functions defined in another module. 
In this case, the standard library functions. 

use standard

Here is a simple type definition that introduces a new type with two components and supplies functions
to create a <* code point2d *> and access its components.

type point2d is x:int, y:int

To allow the type name to be used outside this module we export the type using a special syntax that
omits the return type of the Export:

Export type:point2d

To allow the constructor for points to be used outside the module we export it:

Export point2d(a:int, b:int) point2d

Access to the fields outside the module is granted with: 

Export x(point2d) int

Export y(point2d) int

The following two paragraphs defines an addition and subtraction function on the type point2d. If a
function starts with /keyword function instead of /keyword Function the function is also not available outside the module
.

Function +(a:point2d, b:point2d) point2d point2d(x.a + x.b, y.a + y.b)

Function -(a:point2d, b:point2d) point2d point2d(x.a - x.b, y.a - y.b)

Function %(p:point2d) seq.word "(:(x.p),:(y.p))"

Function testpoint seq.word %(point2d(2, 3) + point2d(4, 5))

/tag <h2> Module to run tests in this document /tag </h2> 

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
 "testseq:(testseq) point2d:(testpoint) testlistset:(testlistset) testdict:(testdict) exampleEncoding:(testExampleEncoding)
  /p geotest:(geotest)"


/tag <h2> Parameterized Module /tag </h2>

A type can have a single type parameter named T. The T can be used anywhere a type can be used.

Generic unbound functions on the type T may be included by using the word unbound as the defining expression. When the parameterized type is used, there must exist a function with the same signature as the unbound
one where T is replaced with the actual type for T.

As an example the follow defines a parameterized set implemented as a sequence 

Module listset.T

use standard

use seq.T

  unbound =(T, T)boolean

  type listset is toseq:seq.T

 Export type:listset.T

  Export toseq(s:listset.T)seq.T

  Function empty:listset.T listset.T listset.empty:seq.T

  Function ∈(ele:T, s:listset.T)boolean ele ∈ toseq.s

 Function +(s:listset.T, ele:T)listset.T if ele ∈ s then s else listset([ ele]+ toseq.s)

  Function tolistset(s:seq.T)listset.T {construct a listset from a sequence.
  (the compiler does not generate any code for this function since it is just a type change)}
for acc = empty:listset.T, ele ∈ s do acc + ele , acc  

  Function ∪(a:listset.T, b:listset.T)listset.T { This union is constructed so if a element is in both a and b the representation in a is use in the result } for acc = a, ele ∈ toseq.b do acc + ele , acc  

  Export isempty(seq.T)boolean

  Export sub(  seq.T,int  )T

  Function lookup(s:listset.T, ele:T)seq.T lookup(toseq.s, ele) 

The purpose of the last three function of the above module will become clear below.

Module testlistset

use standard

use listset.word

Function testlistset seq.word
let set1 = tolistset."A A B C A C B"
let set2 = tolistset."D B E",
if
 toseq.set1 = "C B A"
 ∧ "C" sub 1 ∈ set1
 ∧ "D" sub 1 ∉ set1
 ∧ toseq(set1 ∪ set2) = "D E C B A"
then
"PASS"
else "FAIL"

Sets can be used to implement dictionaries. A dictionary contains entries. Each entry contains a
key and a data component. A type is declared to represent an entry. In this example the key will
be an integer and the data a sequence of words. Entries will be equal if and only if the keys are equal
.

type myentry is key:int, data:seq.word

function =(a:myentry, b:myentry) boolean key.a = key.b

Now a set of entries will be a dictionary. From the mathematical view of the set each entry is an representation
of an integer. The integer 3 could be represented by myentry (3, /sp /tag "X"), myentry (3, /sp /tag" A B C") or and
infinite number of other possibilities. But only one representation will be used in any listset.myentry
.

Looking up an entry in the dictionary is just looking up the representation used in the set.  The last
function in the /em listset module does just that.  The A ∪ B function in the listset module is carefully crafted
so that if an element is in both A and B  the representation of used in A is used in the result.  Thus 
 listset.[myentry(3,/sp /tag  "  X")] ∪ B will redefine the entry in B if it exists.    The expression  B + myentry(3,  /sp /tag" X") or  B ∪ [myentry(3,  /sp /tag" X")] will not redefine the entry in B.  
 By convention, the result  of a binary operation on sets   uses the representation of in the left operand -- not the one on the right.
   
Module testdict

use standard 

use seq.myentry

use listset.myentry

  type myentry is key:int, data:seq.word

  function =(a:myentry, b:myentry)boolean key.a = key.b

  function lookup(a:listset.myentry , i:int)seq.myentry lookup(a, myentry(i,""))

function print(a:listset.myentry)seq.word
 for txt ="", ele ∈ toseq.a do
  txt + "(" + toword.key.ele + "," + data.ele
  + "),"
 , txt >> 1  
 

 
Function testdict seq.word let dict = tolistset.[ myentry(1,"add"), myentry(2,"sub"), myentry(3,"mult")]
let dict2 = tolistset.[ myentry(2,"subtract"), myentry(4,"divide")]
let l1 = lookup(dict, 4) ,
if print.dict = "(3, mult),(2, sub),(1, add)"
 ∧ print.dict2 = "(4, divide),(2, subtract)"
 ∧ isempty.lookup(dict, 4)
 ∧ data.lookup(dict, 2) sub 1  = "sub"
 ∧ print(dict2 ∪ dict)
 = "(1, add),(3, mult),(4, divide),(2, subtract)"then
 "PASS testdict"
 else"FAIL testdict" 



For the type listset.word, the unbound function = in the listset module is bound to the function =(word,word) in the standard module.  
For the type listset.myentry, then unbound = is bound to =(a:myentry, b:myentry)boolean

/tag <h2> >>.T in parameterized module. /tag </h2>

When defining graphs consisting of nodes and edges  the nodes  and edges may be of different type. For example then nodes may be of type T and the edges have a seq.word label.  In this case the type of the edge would be

Module edge.T 

use standard 

type edge is tail:T,head:T,label:seq.word

In parameterized graph module in the Tau release, the parameter is itself a parameterized type 
representing the type of the graph edge.    So within the graph module, T represents the type of the edge and
>>.T references the node type. That is, >>.T references  the parameter of the parameter of the
graph module. 

The follow function would also be needed in the edge module  to be used by the graph module

Function arc(node:T) edge.T 
{used by module graph.edge.T when looking up edges} edge(node,node,"") 

Export head(node:edge.T)  T 
{used by module graph.edge.T }  

Export tail(node:edge.T)  T 
{used by module graph.edge.T }   


/tag <h2> Bindings /tag </h2>

Consider the following example code:

Module B

Function TWO int 2

Module A

use B

use standard

Function f1(p1:int) int let l1 = p1 * TWO, p1 * l1 - THREE

function THREE int 3

Parameters implicitly declare an access function. Example: /keyword function p1 int

Parameters are only visible in the expression that defines the body. Example: p1 is only visible in
the body of f1.

Names of functions are visible within the module. Example: THREE is visible in f1

Functions from another module B are visible in module A, if they are declared using /keyword Function rather than
/keyword function or they are exported and the module A includes a paragraph /keyword use B. Example: the function TWO
is visible in module A and B.

An word of all digits implicitly declares an access function: /keyword function 3 int 

Let definitions are only visible within the second expression in the let statement. 
Let definitions declare an access function: /keyword function l1 <the type of the first expression of the let>. The definition itself returns the type of the second expression.

A function call f1(<exp1>, <exp2>,...)must match exactly one visible function defintion in name, number of parameters and types of the expressions of the arguments.

The type of the expression that defines a function much match the return type of the function.

/tag <h2> Order of evaluation /tag </h2>

The arguments of a function are evaluate from left to right before the function is called.

Not all arguments need to be evaluated. Consider  i > 0 ∧ 300 / i < 10 where ∧ is defined as:
<* block 
function ∧(a:boolean, b:boolean)boolean   if a  then b  else false
*>
 

The compiler will do inline expansion and the above expression becomes <* block if i > 0 then 300 / i < 10 else false *>  If i=0 then the expression   300 / i < 10 is never evaluated.

This behavior is required for the ∧ operator on booleans.


/tag <h2> Encodings /tag </h2>

A type can be mapped to positive integers in an encoding. 

The parameterized module /em encoding.T  defines the following functions for working with encodings. 

Module encode?.T

  use encoding.T

   Export encode(T)encoding.T { will return the encoding } 

  Export   decode(encoding.T)T { will return the value that was encoded } 

  Export   findencode(T) seq.T { will return the empty sequence if the value has not been mapped or a sequence  containing the value that was mapped.} 

   Export encodingdata:T seq.T { list of values that have been encoded.}  
   
  Export valueofencoding(encoding.T) int { the integer value of the encoding}
  
Since the encoding  can be shared by multiple process, modification of  the encoding is a critical section. Also the mapping may contain encodings not assigned by the current process.

Encodings do not exist until it is referenced by a process and the process owns the encoding.

A child process shares any encodings that its parents process has.

Sibling process do not share encodings they own.

An  encoding create by a process is not available to it's parent processes.

 

Module exampleEncoding

This is an example use of an encoding which  encodes sub-expression of a postfix expression 
and then produces code that evaluates any common sub-expressions only once.

use standard

use seq.encoding.myencoding

use encoding.myencoding

use stack.encoding.myencoding

We need a type to encode:

type myencoding is  op:word,operands:seq.encoding.myencoding 

We must define a hash function and = function of the type.

function hash(m:myencoding) int 
 hash(op.m)
 
function =(a:myencoding, b:myencoding) boolean  op.a=op.b ∧ operands.a=operands.b

Note that for a and b of the type myencoding, a = b implies hash (a) = hash (b). 
This must be true for the hash to work correctly. 
The hash function in this example could be improved by including operands in the argument.

 
Function testExampleEncoding seq.word  
  let  R="R1 R2 R3 R4 R5 R6 R7 R8 R9 R11 R12 R13"
  let postfix="5   3 4 + *  3 4 + *  6   3 4 + * +  7 +"
  {encode every subexpression of the postfix expression.  If a sub-expression is used
   more that once it will have the same encoding every time it is used. /br
     Below a stack is used.  The definition is in core.}
  let encodingofpostfix= for  stk=empty:stack.encoding.myencoding,w ∈ postfix do 
    if w ∈ "+*" then  
    push(pop.pop.stk ,encode.myencoding(w, top(stk, 2)))
    else push(stk,encode.myencoding(w,empty:seq.encoding.myencoding))
    , top.stk  
  { all the encodings are now in encodingdata:myencoding. It is now easy to print out 
  instruction that will evaluate common subexpressions only once},
       for acc="" ,idx=1,   e ∈ encodingdata:myencoding do 
       let newacc=acc+"/br"+R sub idx + "=" +if op.e ∈"+,*" then 
                [(R sub (valueofencoding.(operands.e) sub 1))  ,op.e        
                ,(R sub (valueofencoding.(operands.e) sub 2)) ]
      else  [op.e] ,
      next(newacc,idx+1)
      , acc  
      
The testexample output is: <* block R1 = 5 
/br R2 = 3 
/br R3 = 4 
/br R4 = R2+R3 
/br R5 = R1 * R4 
/br R6 = R5 * R4 
/br R7 = 6 
/br R8 = R7 * R4 
/br R9 = R6+R8 
/br R11 = 7 
/br R12 = R9+R11 
/br *>
      
Consider the sequence of calls, C, in the execution of the program to the function encode. Let S be the sequence of T where S_i is the value passed as parameter in call C_i Let E be the sequence of results where E_i = the result of call C_i.

Then <* block S_i = S_j if and only if encoding(E_i)= encoding(E_j)*> and <* block decode(E_i)is identical to S_j where j = min t where S_t = E_i *> and <* encoding(E_i)> 0 *>


/tag <h2> Process statement /tag </h2>

Process are included in Tau for three reasons.

Using multiple processes on multi-core processors can be used to obtain results faster.

Process allow temporary space used to calculate the result to be reclaimed. This is the only way for heap space to be reclaimed in Tau.

Process allow abnormal events to be captured and reported. The following code snippet show how to capture an abnormal event.

Module testprocess

use process.int

use standard

 function myprocess(a:int)int 
   assert a > 0   report "invalid" ,
   a sup 3

  function useprocess(i:int)int 
{ Note that the result type of this function matches the parameter 
  in the use clause above. This provides access to 
  the  psuedo-function   process below and allows a spawned process 
  of type process.int to be created
  from the function   myprocess }
  let a = process.myprocess.i ,
  if aborted.a 
    then  assert message.a ="invalid"   report "new message" ,
   0 
  else result.a


The follow functions interact with the spawned process and blocks to wait for the spawned process to finish.

Module process?.T

use process.T

use standard

Export aborted(process.T ) boolean { true if the process was aborted as with an assert statement }  

Export message(process.T ) seq.word  { message return when process was aborted } 

Export result(process.T) T { result return upon successful completion. }  

The spawning process cannot terminate until all of it child process complete, because it may have allocated space and passed it to a child process as a parameter. 


/tag <h2> Defining Sequences /tag </h2>

Some times it is usefully to define a new type of sequence.  Here we defined a geometric sequence moduled after the arithmetic seq
define in seq1.T


Module geometricseq.T

All sequences must be in a parameterized Module.

use standard

We need some operations on T. 

unbound *(T,T) T

unbound sup(T,int) T

type geometricseq is   sequence,step:T, start:T

The above type is recognized as a sequence as the first element of the type is sequence.

A function /em length (myseq) is implicitly defined to access the length of geometricseq

As with any parameterized module  a type definition   
must contain an element that uses T so that multiple 
instances of the module does not produce duplicate symbols.

Every sequence must have a#function defined on it:

Function sequenceIndex(s:geometricseq.T, i:int) T start.s *  (step.s) sup (i-1)

We need a constructor of our sequence. Note the use of a toseq function. 
This is defined implicitly by the sequence type definition to change the type 
from geometricseq.T to seq.T

Function geoseq(length:int, step:T, start:T) seq.T
toseq.geometricseq(length, step, start)

Module geotest 

use standard

use geometricseq.real

use geometricseq.int

use real


Function geotest seq.word
  "first 10 powers of 2="+%.geoseq(10,2,2)
  +"/br first 10 powers of 0.5="+%.geoseq(10,0.5,0.5)
  
The following are needed to define %(seq.int) and  %(seq.real).

use seq1.int

use seq1.real

Function  %(a:real) seq.word %(10,a)

End of module geotest.


/tag <h2> Tail Recursion /tag </h2>

A function is tail recursive if the last function called is itself. A compiler can take advantage of this and reuse the activation record on the call stack resulting in less space taken up by the stack during execution.

Sometimes a recursive function can be rewritten to make it tail recursive. Consider the following function:

 use seq.int

  function reverse2(l:seq.int)seq.int 
  if isempty.l    then l   else reverse2.subseq(l, 2, n.l)+  l sub 1

The last call in this function is to +. Here is a rewritten version that is tail recursive:

  function reverse3(l:seq.int, accumalator:seq.int)seq.int 
 if isempty.l then accumalator   else reverse3(subseq(l, 2, n.l), accumalator + l sub 1)

  function reverse3(l:seq.int)seq.int reverse3(l, empty:seq.int)

Now reverse3 is the last function called.

Making the function tail recursive is not the only way to reduce the stack size. The follow version
uses O (ln n) instead of O (n) where n is the length of the sequence.

function reverse4(l:seq.int) seq.int
if n.l < 2 then
l
else reverse4.subseq(l, n.l / 2 + 1, n.l) + reverse4.subseq(l, 1, n.l / 2)

Perhaps the best way to reverse a sequence is to use

Function reverse5(s:seq.int) seq.int for acc = empty:seq.int, e ∈ s do [e] + acc, acc

In this case the tau compiler will remove the bounds checking when indexing the sequence. If the sequence
was built up out of smaller sequences, it may also break the sequence into the smaller parts and process
them separately. 


END

