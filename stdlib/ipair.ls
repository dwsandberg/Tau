Module ipair.T

use stdlib

type ipair is record index:int, value:T

Export type:ipair.T

Export index(ipair.T)int

Export value(ipair.T)T

Export ipair(i:int, t:T)ipair.T