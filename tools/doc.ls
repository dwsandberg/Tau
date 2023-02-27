<* none <style><!--span.code1 { border:solid; border-width: thin;} 
 span.code { font-family:italic;}--> </style> 
*>

<* code this is a test *>

<* section The Tau Programming Language *>

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

Instruction for downloading and install Tau in  <* none <a href="install.html"> here </a> *> if you would
like to try out the examples below for yourself.

<* section Lexical level *>

A program is represented as a sequence of characters. The character encoding is assume to be unicode represented in UTF8 format. The program is broken into a sequence of paragraphs where one or more blank lines separate the paragraphs.

Paragraphs that do NOT start with /keyword type, /keyword use, /keyword Module,
 /keyword module, /keyword Function, /keyword function, /keyword unbound,  or /keyword Export are always treated as comments.

Each paragraph is broken into words. One or more spaces separate the words. A single line break is treated the same as a space. 
The characters ()+,-.:=[]{}^_" are all treated as if they have an implied space before and after them so they are words formed from a single character. For example,/ldq a /sp +/sp b" is equivalent to /ldq    a+b"; but /ldq  a * b" is not equivalent to /ldq  a*b". 
  
  A period followed by a space is treated as a separate word from a period not followed by a space. 
  This allows a period at the end of a sentence to be distinguished from a period in google.com. 
  
The colon is treated the same as a period since a space normally follows a colon but not in  3:30PM.

A word sequence literal is double-quoted. For Example:  /ldq  This is a string Literal."  

To include a double quote within a string use  a syntactical short  hand.  For example:
  <* block /ldq  hello world without quotes; $(dq) hello world $(dq) with quotes"   *> 
  is the same as 
  writing 
  <* block  /ldq  hello world without quotes;"/sp+/sp dq /sp+/sp /ldq hello world"  +/sp dq /sp+"/nosp   with quotes"   *>
  Since $(...) can receive any expression we could also write
  <* block "/nosp hello world without quotes $(dq./ldq hello world") with quotes" *>
  Since /ldq $(" functions as an escape in strings, it can be include within a string
  as "/nosp  $(/ldq  $")( " Note that just the /dq  $" is escaped as /ldq    $("/nosp $(")" will raise an error 
  because the escape in the inner qoute is not properly formed.
  

An integer literal is represented by a sequence of words where each word only contains digits or the no break space. 
A real number is two integer separated by a period. 
For example <* code 0.0 *> and <* code 10.01 *> are real numbers 
where <* code 00 *> and <* code 1001 *> are integers.

For easy entry, ASCII equivalents for ≤ ≥ ≠ ∧ ∨ ⊻ ∈ ∉ ∩ ∪ are 
<* code /le /ge /ne /and /or /xor /in /nin /cap /cup *> respectively.

Be careful to insert necessary spaces around operators. For example, 
<* code 8*9 *> is incorrect and should be written as <* code 8 * 9 *>, or <* code (8)  *(9) *>.



<* section Converting words to UTF8 *>

A sequence of tau words must be transformed back to UTF8 format to communicate with the outside world. 
 When a file is read the white space is striped out and must be added back in. 

The basic rules  for   adding  spaces is to  add a space 
after each word except when :
/br 1. If the word is /sp+-_.. :^/sp then the space before and after the word is suppressed. 
/br 2. If the word is /sp)]}," then the space before the word is suppressed.
/br 3. If the word is ([{ then the space after the word is suppressed.

Line breaks are handled by inserting formatting words.  The simplest formatting rules are
 /br  for a line break and   /p for a paragraph break. 

Since an opening quote mark should be treated differently than a closing quote mark and the ASCII character set
does not distinguish between opening and closing quote marks, /ldq is insert a double quote
Suppressing the space after.  Additional /sp will force a space and /nosp will suppress the
Space normally added after a word. 

The format words are interpreted differently when producing plain text or HTML.  For example, /keyword /p produces LF LF for plain text and 
<* LF <p> *>.  Different functions are provide to do this.   When creating files from seq.word  for output, if file extension is html then the output is HTML 
otherwise plain text.

<* section Expressions *>

The follow are treated as   infix binary operators. The operators on the same line are the same precedence and higher precedence than those on the following line.
/br _^
/br unary minus
/br * / mod ∪ ∩ \
/br  +-∈ ∉
/br = < > >1 >2 ≤ ≥ ≠ >> <<
/br ∧
/br ∨ ⊻

Parentheses are used to override the default precedence.  Note that the operators ∪ ∩ \ which are commonly used for set union, intersection and differences all have that same precedence.

Procedure calls are of the form <* code  f1 /nosp(p1, p2, …, pn)*>. 
<* code   f1 /nosp() *> is illegal and should be written f1. To avoid excessive parentheses in expressions 
<* code f1 /nosp(p1)*> is equivalent to <* code  f1.p1 /nosp *>. 
The precedence of /sp. is between the /sp_ and the *.

The operators ≤ ≥ ≠ are abbreviations for   not /nosp(a > b) ,   not /nosp( a < b ),  not /nosp(a = b) respectively. 


The compilation unit in tau is  a library. A library contains modules. A module is a sequence of paragraphs with this first paragraph starting with the word /keyword module.

A paragraph is a sequence of words. Paragraphs that do NOT start with /keyword type, /keyword use, /keyword Library,
 /keyword module, /keyword Function /keyword function, /keyword unbound,  or /keyword Export are always treated as comments.

(x)* repeat 0 or more times
/br (x|y)  select x or y 
/br A backslash before ( or ) removes the regular expression meaning.

The non-terminals are P TYPE L E B C  representing Paragraphs, types, parameter lists, expressions, blocks, and comments

The right hand side of the grammar rules are described with a regular expressions syntax
where /br (x)*  means repeat x 0 or more times;
/br (x | y)  means select x or y. y can be empty;
/br A backslash before ( or ) removes the regular expression meaning.


Reserved words are words included on the right hand side of the grammar rules
excluding the words: use type Export unbound Function function is number and word.


The meaning of /em word is context sensitive.
/br For the last E rule (string literals)  /em word does not include " or if it is ( preceded by $.
/br For the C rule, /em word does not include {}.
/br For rules for P with /keyword Function , /keyword function and /keyword Export, 
/em word  includes binary operators but not words starting with a digit or are reserved.
(To allow binary operators to be user defined.)
/br Other usage  of /em word excludes reserved words, binary operations and words starting with a digit. 
 
The /em number represents a word of all digits or 0x or 0X followed by hexadecimal digits.

The syntax for non-comment paragraphs is 
<* block /em P→ /keyword Module /em word.T | /keyword Module /em word  
/br /em P→ /keyword use /em TYPE 
/br /em P→ /keyword type /em word /keyword is  /em L  /em C  
/br /em P→  /keyword Export   type:/em TYPE   /em C 
/br /em P→ ( /keyword Export |   /keyword unbound) /em word(:/em TYPE |) (\(/em L \)|)   /em TYPE    /em C 
/br /em P→ (/keyword  Function | /keyword function ) /em word(:/em TYPE |)( \(/em L \) |)   /em TYPE  /em B
/br /em TYPE → /em word (./em word)*
/br /em L → (/em C /em word:|) /em TYPE ( , (/em C /em word:|) /em TYPE )*
/br /em E →  /em word (:/em TYPE |) (\(/em E ( , /em E )*\)) 
/br /em E → /keyword if /em E /keyword then /em B /keyword else /em B ( /keyword /if | )
/br /em E →\(/em E \)/br /em E → /em E  <binary op> /em E  
/br /em E → -/em E /br /em E → /em word./em E  
/br /em E →   /em C /em E
/br /em E → [ /em E ( , /em E )]
/br /em E → /keyword  for /em word = /em E, ( /em word = /em E , )* /em word ∈ /em E /keyword do 
(while /em E |)/keyword do /em B   /keyword /do /em E (/keyword /for |)  
/br /em E  → number (. number|)
/br /em E → " (/em word| $\(E\))*"
/br /em B  →   (/keyword let <let name> = /em E | /keyword assert /em E /keyword report /em B 
| /em { (/em C | /em word)*  },   )* E
/br  /em C → ({ (/em C | /em word)*  } |)*

The type of an expression can always be inferred from the sub-expressions. For example, 1.0 <* code + 5.0 *> is of type real, <* code 1 * 8 *> is of type int, 
and <* code 1.0 = 8.0 *> is of type boolean.


Comments are traditionally defined at the lexical level. In tau they are defined as a prefix operator so that they can easily be included in a parse tree.

A /keyword let statement in a function allows an name to be given to an expression so the name can be used in the expression that follows. 
A /keyword let statement DOES NOT define a variable that can change values.


<* section Module Standard *>

A module is a collection of functions and types.

The module standard defines often used function and types. A full list of
functions is  <* none <a href ='./stdlibdoc.html#standard'>  here </a>  *>
Many of the functions are defined in other modules and only exported from the standard module. A few note worth types and functions are list below.

The types /em int and /em real are implement by the underlying hardware and have the usual operations. 

The type boolean has operators:∧ ∨ /em not /em true and /em false. The second operator of ∧ and ∨ is evaluated if and only if the first operator does not determine the result.

This document itself can be feed directly to a Tau compiler.  Modules  with names ending in a question mark like in the next paragraph  are introduced solely for the purpose of allowing the document to compile. 

Module standard?

The paragraph below makes visible in module standard?  the function and types in the module standard.

use standard

For working with total orderings a type /em ordering with the values /em LT /em EQ and /em GT are defined. There is a binary operaator >1 in the standard module that could be defined as

Function >1(a:int,b:int) ordering if a > b then GT else if a=b then EQ else LT

 An ∧ operator on orderings is defined as

  Function ∧(a:ordering, b:ordering)ordering 
  if a = EQ   then b   else a

By convention function that begin with a %  have a return type of seq.word and supply a human readable representation.   Two such functions are defined in the standard module:

Export %(n:int) seq.word  

Export %(w:word) seq.word  


<* section Sequences *>

A sequence is a function whose domain is the integers and whose range is some type. 
A literal for a sequence of integers is coded as <* core [ 2, 4, 8, 16, 32]
*>  and has a type of <* code seq.type *>.  

A sequence of characters in double quotes does not represent a sequence of characters but a sequence of words. 
 <* code “Hello World!” *> represent two words.

The code <* code [ “Hello”_1, ”World!”_1] *> is equivalent to 
<* code  “Hello World!” *>

Sequences have the following functions defined in a parameteized module named
<* code  seq.T *> where T can be any type. 

Module seq?.T 

use seq.T

Export _(a:seq.T,i:int) T { Return ith element of sequence.  a_1 is the first element}

Export empty:seq.T seq.T  { Returns the sequence of type seq.T with zero elements}

Export +(a:seq.T, b:seq.T) seq.T {Concatenation operator} 
  
Export subseq(s:seq.T, start:int, stop:int)seq.T  {Obtain sub-sequence}

Export =(a:seq.T, b:seq.T) boolean {Test to see if a and b represent the same sequence.
This function requires a function =(T,T)boolean}

The module <* code standard *> exports the above  functions with T replace by the type <* code word *>

The function below is an example of using these functions.

Module testseq

use standard

Function testseq seq.word
let s1 = "This is a test sequence with 9 words." ,
if length.s1 = 9 ∧ s1_3 = "a"_1 ∧ subseq(s1, 4, 5) = "test sequence"
∧ subseq(s1, 4, 3) = empty:seq.word
∧ subseq(s1, 1, 5) + subseq(s1, 6, length.s1) = s1 
∧ [ "Hello"_1, "World!"_1] = "Hello World!" 
∧  empty:seq.word="" 
∧ subseq([11,12,13,14],1,2)=[11,12] then
 "PASS"
else "FAIL"


<* section Iteration *>

An operation can be performed on each element of a sequence.  The following sums a sequence:

 function sum(s:seq.int) int  for   accumulator=0 ,e ∈ s    do accumulator+e    /do accumulator /for

More than one accumulator is allowed. The following takes the average of the sequence

  function average(s:seq.int) int for   count=0,sum=0, e ∈ s   do next(count+1,sum+e)    /do  sum / count /for

For each element of the sequence the  expression after the /keyword do is executed giving new values to the accumulators. 

It is possible to not examine all elements of the sequence.  The following stops examining elements when /em ele is found

 
function /in(s:seq.int,ele:int) boolean   
  for found = false, i ∈ s   while not.found   do ele = i  /do found /for
  

<* section User Types *>


The module below defines a user defined type.

Module point2d

The follow paragraph that begins with /keyword use allows reference to functions defined in another module. In this case, the standard library functions. 

use standard

Here is a simple type definition that introduces a new type with two components and supplies functions to create a <* code point2d *> and access its components.

type point2d is x:int, y:int

To allow the type name to be used outside this module we export the type  using a special syntax that omits the return type of the Export:

 Export type:point2d

To allow the constructor for points to be used outside the module we export it:

Export point2d(a:int, b:int)point2d 

Access to the fields outside the module is granted with: 

 Export x( point2d  )int 

 Export y( point2d ) int   


The following two paragraphs defines an addition and subtraction function on the type point2d. 
If a function starts with  /keyword  function  instead of /keyword   Function  the function is also not available outside the module.


Function +(a:point2d, b:point2d)point2d point2d(x.a + x.b, y.a + y.b)

Function-(a:point2d, b:point2d)point2d point2d(x.a - x.b, y.a - y.b)

Function %(p:point2d)seq.word  "( $(x.p) , $(y.p) )"

Function testpoint seq.word %(point2d(2, 3)+ point2d(4, 5))


<* section Module to run tests in this document *>

Module testdoc

use standard

use file

use testseq

use point2d

use testlistset

use testdict

use exampleEncoding

use  geotest

Function testdoc(input:seq.file,o:seq.word) seq.file
{ }[file(o,"testseq $(testseq) point2d $(testpoint) testlistset $(testlistset) testdict $(testdict) exampleEncoding $(testExampleEncoding) /p geotest  $(geotest)")]




<* section Parameterized Module *>

A type can have a single type parameter named T. The T can be used anywhere a type can be used.

Generic unbound functions on the type T may be included by using the word unbound as the defining expression. When the parameterized type is used, there must exist a function with the same signature as the unbound one where T is replaced with the actual type for T.

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

  Function tolistset(s:seq.T)listset.T {construct a listset from a sequence}
for acc = empty:listset.T, ele ∈ s do acc + ele /do acc /for

  Function ∪(a:listset.T, b:listset.T)listset.T { This union is constructed so if a element is in both a and b the representation in a is use in the result } for acc = a, ele ∈ toseq.b do acc + ele /do acc /for

  Export isempty(seq.T)boolean

  Export_(seq.T, int)T

  Function lookup(s:listset.T, ele:T)seq.T lookup(toseq.s, ele) 

The purpose of the last three function of the above module will become clear below.

Module testlistset

use standard

use listset.word


Function testlistset seq.word 
let set1 = tolistset."A A B C A C B"
let set2 = tolistset."D B E" ,
if toseq.set1 = "C B A" ∧ first."C" ∈ set1
 ∧ first."D" ∉ set1
 ∧ toseq(set1 ∪ set2) = "D E C B A"then
 "PASS "
 else"FAIL"

Sets can be used to implement dictionaries.   A dictionary contains entries.  
Each entry contains a key and a data component.  A type is declared to represent an entry.  In this example the key will be an integer and the data a sequence of words. 
Entries will be equal if and only if the keys are equal.

 type myentry is key:int, data:seq.word

 function =(a:myentry, b:myentry)boolean key.a = key.b

Now a set of entries will be a dictionary.   From the mathematical view of the set each entry is an representation of an integer.  The integer 3 could be represented by
 myentry(3,/so "X") , myentry (3,/so "A B C") or and infinite number of other possibilities.  But only one representation will be used in any listset.myentry.

Looking up an entry in the dictionary is just looking up the representation used in the set.  The last
function in the /em listset module does just that.  The A ∪ B function in the listset module is carefully crafted
so that if an element is in both A and B  the representation of used in A is used in the result.  Thus 
 listset.[myentry(3,/so "X")] ∪ B will redefine the entry in B if it exists.    The expression  B + myentry(3, /so "X") or  B /cup [myentry(3, /so "X")] will not redefine the entry in B.  
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
 /do txt >> 1 /for
 

 
Function testdict seq.word let dict = tolistset.[ myentry(1,"add"), myentry(2,"sub"), myentry(3,"mult")]
let dict2 = tolistset.[ myentry(2,"subtract"), myentry(4,"divide")]
let l1 = lookup(dict, 4) ,
if print.dict = "(3, mult),(2, sub),(1, add)"
 ∧ print.dict2 = "(4, divide),(2, subtract)"
 ∧ isempty.lookup(dict, 4)
 ∧ data.lookup(dict, 2)_1 = "sub"
 ∧ print(dict2 ∪ dict)
 = "(1, add),(3, mult),(4, divide),(2, subtract)"then
 "PASS testdict"
 else"FAIL testdict" 



For the type listset.word, the unbound function = in the listset module is bound to the function =(word,word) in the standard module
For the type listset.mytype, then unbound = is bound to =(a:myentry, b:myentry)boolean


<* section Order of evaluation *>

The arguments of a function are evaluate from left to right before the function is called.

Not all arguments need to be evaluated. Consider  i > 0 ∧ 300 / i < 10 where ∧ is defined as:

function ∧(a:boolean, b:boolean)boolean   if a  then b  else false

 

The compiler will do inline expansion and the above expression becomes <* block if i > 0 then 300 / i < 10 else false *>  If i=0 then the expression   300 / i < 10 is never evaluated.

This behavior is required for the ∧ operator on booleans.

<* section Bindings *>

Consider the following example code:

Module B

Function TWO int 2

Module A

use B

use standard

Function f1(p1:int)int 
  let l1 = p1 * TWO ,
   p1 * l1 - THREE

function THREE int 3

Parameters implicitly declare an access function. Example: /keyword function p1 int 

Parameters are only visible in the expression that defines the body. Example: p1 is only visible in the body of f1.


Names of functions are visible within the module. Example: THREE is visible in f1

Functions from another module B are visible in module A, if they are declared using /keyword Function 
rather than /keyword function or they are exported and the module A includes a  paragraph /keyword use B.  Example: the function TWO is visible in  module A and B.

An word of all digits implicitly declares an access function: /keyword function 3 int 

Let definitions are only visible within the second expression in the let statement. 
Let definitions declare an access function: /keyword function l1 <the type of the first expression of the let>. The definition itself returns the type of the second expression.

A function call f1(<exp1>, <exp2>,...)must match exactly one visible function defintion in name, number of parameters and types of the expressions of the arguments.

The type of the expression that defines a function much match the return type of the function.



<* section Encodings *>

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
 
function =(a:myencoding, b:myencoding) boolean  op.a=op.b /and operands.a=operands.b

Note that for a and b of the type myencoding, a = b implies hash (a) = hash (b). 
This must be true for the hash to work correctly. 
The hash function in this example could be improved by including operands in the argument.

 
Function testExampleEncoding seq.word  
  let  R="R1 R2 R3 R4 R5 R6 R7 R8 R9 R11 R12 R13"
  let postfix="5   3 4 + *  3 4 + *  6   3 4 + * +  7 +"
  {encode every subexpression of the postfix expression.  If a sub-expression is used
   more that once it will have the same encoding every time it is used. /br
     Below a stack is used.  The definition is in core.}
  let encodingofpostfix= for  stk=empty:stack.encoding.myencoding,w /in postfix do 
    if w /in "+*" then  
    push(pop.pop.stk ,encode.myencoding(w, top(stk, 2)))
    else push(stk,encode.myencoding(w,empty:seq.encoding.myencoding))
    /do top.stk /for
  { all the encodings are now in encodingdata:myencoding. It is now easy to print out 
  instruction that will evaluate common subexpressions only once},
       for acc="" ,idx=1,   e /in encodingdata:myencoding do 
       let newacc=acc+"/br"+R_idx+ "=" +if op.e /in"+,*" then 
                [R_(valueofencoding.(operands.e)_1) ,op.e        ,R_(valueofencoding.(operands.e)_2)]
      else  [op.e] ,
      next(newacc,idx+1)
      /do acc /for
      
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
/br R12 = R9+R11 <* /br
      
Consider the sequence of calls, C, in the execution of the program to the function encode. Let S be the sequence of T where S_i is the value passed as parameter in call C_i Let E be the sequence of results where E_i = the result of call C_i.

Then <* block S_i = S_j if and only if encoding(E_i)= encoding(E_j)*> and <* block decode(E_i)is identical to S_j where j = min t where S_t = E_i *> and <* encoding(E_i)> 0 *>


<* section Process statement *>

Process are included in Tau for three reasons.

Using multiple processes on multi-core processors can be used to obtain results faster.

Process allow temporary space used to calculate the result to be reclaimed. This is the only way for heap space to be reclaimed in Tau.

Process allow abnormal events to be captured and reported. The following code snippet show how to capture an abnormal event.

Module testprocess

use process.int

use standard

 function myprocess(a:int)int 
   assert a > 0   report "invalid" ,
   3^a

  function useprocess(i:int)int 
{ Note that the result type of this function matches the parameter 
  in the use clause above. This provides access to 
  the  psuedo-function   process below and allows a spawned process 
  of type process.in to be created
  from the function   myprocess }
  let a = process.myprocess.i ,
  if aborted.a 
    then  assert message.a ="invalid"   report "new message" ,
   0 
  else result.a


The follow function interact with the spawned process and blocks to wait for the spawned process to finish.

Module process?.T

use process.T

use standard

Export aborted(process.T ) boolean { true if the process was aborted as with an assert statement }  

Export message(process.T ) seq.word  { message return when process was aborted } 

Export result(process.T) T { result return upon successful completion. }  

The spawning process cannot terminate until all of it child process complete, because it may have allocated space and passed it to a child process as a parameter. 


<* section Defining Sequences *>

Some times it is usefully to define a new type of sequence.  Here we defined a geometric sequence moduled after the arithmetic seq
define in otherseq.T


Module geometricseq.T

All sequences must be in a parameterized Module.

use standard

We need some operations on T. 

unbound *(T,T) T

unbound ^(T,int) T

type geometricseq is   sequence,step:T, start:T

The above type is recognized as a sequence as the first element of the type is sequence.

A function /em length (myseq) is implicitly defined to access the length of geometricseq

As with any parameterized module  a type definition   
must contain an element that uses T so that multiple 
instances of the module does not produce duplicate symbols.

Every sequence must have a_function defined on it:

Function _(s:geometricseq.T, i:int) T start.s *  (step.s) ^ (i-1)

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

use otherseq.int

use otherseq.real

Function  %(a:real) seq.word print(10,a)

End of module geotest.


<* section Tail Recursion *>

A function is tail recursive if the last function called is itself. A compiler can take advantage of this and reuse the activation record on the call stack resulting in less space taken up by the stack during execution.

Sometimes a recursive function can be rewritten to make it tail recursive. Consider the following function:

 use seq.int

  function reverse2(l:seq.int)seq.int 
  if isempty.l    then l   else reverse2.subseq(l, 2, length.l)+ l_1

The last call in this function is to +. Here is a rewritten version that is tail recursive:

  function reverse3(l:seq.int, accumalator:seq.int)seq.int 
 if isempty.l then accumalator   else reverse3(subseq(l, 2, length.l), accumalator + l_1)

  function reverse3(l:seq.int)seq.int reverse3(l, empty:seq.int)

Now reverse3 is the last function called.

Making the function tail recursive is not the only way to reduce the stack size. The follow version uses O(ln n) instead of O(n)where n is the length of the sequence.

  function reverse4(l:seq.int)seq.int 
 if length.l < 2  then l   else reverse4.subseq(l, length.l / 2 + 1, length.l)+ reverse4.subseq(l, 1, length.l / 2)

Perhaps the best way to reverse a sequence is to use

  Function reverse5(s:seq.int)seq.int    
  for acc=empty:seq.int,e ∈ s   do [e]+acc /do acc /for


In this case the tau compiler will remove  the bounds checking when indexing the sequence.  
If the sequence was built up out of smaller sequences, it may also  break the sequence into the smaller parts and process them separately. 


<* section markup *>

<* table Markup Commands
/row Example /cell with format /cell note
/row first /keyword /p second   /cell /   first /p second  /cell paragraph break
/row first /keyword /br second  /cell  first /br second /cell line break
/row /keyword /em example /cell /em example  /cell
/row /keyword /strong example /cell /strong example  /cell
/row /keyword /keyword example /cell /keyword example  /cell
/row /keyword <* /keyword literal this is an example  /keyword *> /cell <* literal  this is an example *>  /cell
/row /keyword <* /keyword keyword this is an example  /keyword *>  /cell <* keyword this is an example  *>  /cell
/row /keyword <* /keyword comment this is an example  /keyword *>; /cell <* comment this is an example  *>  /cell
/row parent /br block /keyword <* /keyword block Indented block. /br /keyword /br second line /keyword *> 
/cell parent block <* block Indented block. /br second line *> 
/cell   Indented block 
/row /keyword <* /keyword none <hr/> /keyword *> 
/cell  <* none <hr> *>  /cell 
/row /keyword <* /keyword table <* none <caption> <rows of table>  *> /keyword *> /cell /cell Defines a table 
/row  /keyword /row../keyword /cell../keyword /cell..  /cell /cell Defines a row of with three columns. 
/br Must be placed within table. 
/row /keyword <* /keyword table    Sample   Table 
/br /keyword /row   1 /keyword /cell 2 /keyword /cell 3
/br /keyword /row   3 /keyword /cell 4 /keyword /cell 5
/keyword *>
/cell
<* table    Sample  Table 
 /row   1 /cell 2 /cell  3 
 /row   3 /cell 4 /cell 5  
  *>
/cell
*> 

END

