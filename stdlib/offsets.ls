module offsets

use stdlib

type offset is record TSIZE:int, LIT:int

Function LIT(offset)int export

Function Tsize offset offset(1, 0)

Function offset(i:int)offset offset(0, i)

Function =(a:offset, b:offset)boolean TSIZE.a = TSIZE.b ∧ LIT.a = LIT.b

Function print(a:offset)seq.word 
 [ toword.LIT.a]+ if TSIZE.a = 0 then""else"TSIZE"+ toword.TSIZE.a

Function +(a:offset, b:offset)offset offset(TSIZE.a + TSIZE.b, LIT.a + LIT.b)

Function +(s:seq.int, b:offset)seq.int s + LIT.b

Function compose(a:offset, b:offset)offset offset(TSIZE.a * TSIZE.b, TSIZE.a * LIT.b + LIT.a)

