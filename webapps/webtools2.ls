Module webtools2

use file

use standard

use compilerfrontT.callconfig

use symbol2

Export compilerFront:callconfig(seq.word, seq.file, seq.word, seq.word) midpoint

/use standard

/use symbol2

Export type:callconfig

type callconfig is a:int

Function callfunc:callconfig(ctsym:symbol, typedict:typedict, stk:seq.int) seq.int
if ctsym = symbol(internalmod, "+", typeint, typeint, typeint) then
[1#stk + 2#stk]
else if ctsym = symbol(internalmod, "*", typeint, typeint, typeint) then
[1#stk * 2#stk]
else if ctsym = symbol(internalmod, "-", typeint, typeint, typeint) then
[1#stk - 2#stk]
else if ctsym = symbol(internalmod, "/", typeint, typeint, typeint) then
[1#stk / 2#stk]
else if
 ctsym = symbol(internalmod, "=", typeint, typeint, typeboolean)
  ∨ ctsym = symbol(internalmod, "=", typeboolean, typeboolean, typeboolean)
then
[if 1#stk = 2#stk then 1 else 0]
else empty:seq.int 