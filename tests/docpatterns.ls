// // patterns /id /scan



Example of   Renaming Function /h1

Module patterns

precedence sub for #

use standard

use seq.*

use set.*

The pattern3 transformation will change the value of the original to
look like the value of changed in the procedure below.

function example3(i:int, x:int) int
let original = [i + 1, x + 1, 3 + 1, 3 * 1 + 1, i + x + 1]
let changed = [inc.i, inc.x, inc.3, inc(3 * 1), inc(i + x)],
0

To specify this transformation, we must first define the inc function.

function inc(i:int) int i + 1

We will use a single parameterized pattern specified with the function below. 

Function pattern3(t:int) seq.int [ t+1, inc.t]

The result type of the function is the sequence of the type of the expression
being translated. It this case the expression type is type int so the
result type of pattern3 is seq.int. The parameter t of pattern3 will match
any expression of type int.  the pattern3 will be applied five times and
t will take on the values i, x, 3, 3 * 1 ∧ i+x. 

The body of pattern3 is of the form [old,new] where old is the old
expression and new is the new expression. The t in the new expression will be replaced with what t matches in the old expression. 

Expressions can also be transformed for a function in parameterized modules. To do this, one must define the type * to represent the parameterized type T. 

type * is a:seq.int

Function pattern4(s:seq.*) seq.*
{use a separate function to get the first element of a sequence}
[  s sub 1, first.s]

Function pattern5(s:seq.*,i:int) seq.* {switches order of parameters} [i # s, s sub i] 
  
The parameterized module /em firstop defines the first function and the function that uses
a different parameter order. The definition is below. 

Some uses are needed to make the functions and types used in patterns and 5 available in the module.

use seq.*

use firstop.*

Pattern5 and pattern6 transformation will change the value of the original to
look like the value of changed in the procedure below.  

function example4 int
let original = 2 # [1, 2, 3] + 1 # [3, 4, 5]
let changed = [1, 2, 3] sub 2 + first.[3, 4, 5],
0

The use below is included so example4 will compile. 

use firstop.int


Module firstop.T

use seq.T

Function first(s:seq.T) T   sub(s,1)

/Function  sub ( s:seq.T,i:int) T sub(s,i)

Function  # ( i:int, s:seq.T) T sub(s,i)
