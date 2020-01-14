Module ipair.T

use stdlib

type ipair is record index:int, value:T

Function type:ipair.T seq.word export

Function index(ipair.T)int export

Function value(ipair.T)T export

Function ipair(i:int, t:T)ipair.T export

