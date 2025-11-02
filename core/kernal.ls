Module kernal

Export type:boolean

Export type:char

Export toint(char) int

Export char(int) char

Export word(int) word

Export type:ordering

Export toint(ordering) int

Export type:word

Export rawvalue(word) int

type char is toint:int

type ordering is toint:int

Function EQ ordering ordering.1

Function GT ordering ordering.2

Function LT ordering ordering.0

Function =(a:char, b:char) boolean toint.a = toint.b

Function =(a:word, b:word) boolean
{OPTION COMPILETIME}
rawvalue.a = rawvalue.b

Function >1(a:ordering, b:ordering) ordering
{possible results are: EQ GT LT}
toint.a >1 toint.b

Function =(a:ordering, b:ordering) boolean toint.a = toint.b

---------

Builtin representation(a:real) int

Function -(i:int) int 0 - i

Builtin >1(a:int, b:int) ordering

Builtin +(a:int, b:int) int

Builtin -(a:int, b:int) int

Builtin *(a:int, b:int) int

Builtin /(a:int, b:int) int

Builtin =(a:int, b:int) boolean

Function abs(x:int) int if x < 0 then 0 - x else x

Function mod(x:int, y:int) int if x < 0 then x - x / y * y + y else x - x / y * y

Builtin >(a:int, b:int) boolean

Function <(a:int, b:int) boolean b > a

Function between(i:int, lower:int, upper:int) boolean i ≥ lower ∧ i ≤ upper

Function sup(x:int, n:int) int
{* nth power of i}
if n = 0 then 1
else if n = 1 then x
else if n = 2 then x * x
else if n = 3 then x * x * x
else
 assert n > 3 report "negative powers are not implemented"
 for acc = x * x * x * x, k = 4 while k < n do next(acc * x, k + 1),
 acc

Function max(a:int, b:int) int if a > b then a else b

Function min(a:int, b:int) int if a < b then a else b

--------

type boolean is tointx:int

Builtin true boolean

Builtin false boolean

Builtin not(a:boolean) boolean

Builtin =(a:boolean, b:boolean) boolean

Function ∧(a:boolean, b:boolean) boolean if a then b else false

Function ∨(a:boolean, b:boolean) boolean if a then true else b

Builtin stacktrace seq.word

type word is rawvalue:int

-----------

Export type:timestamp

Export seconds(timestamp) int

Export timestamp(int) timestamp

type timestamp is seconds:int 
