Module ipair.T

use stdlib

type ipair is record index:int, value:T

Export type:ipair.T  

Function index(ipair.T)int export

Function value(ipair.T)T export

Function ipair(i:int, t:T)ipair.T export