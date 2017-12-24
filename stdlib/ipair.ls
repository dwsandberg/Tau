Module ipair(T)

type ipair is record index:int, value:T

use stdlib

Function index(ipair.T)int export

Function value(ipair.T)T export

Function ipair(i:int, t:T)ipair.T export

------------------------------

