Module JS.T

use bitcast.JS.T

use bitcast.int

use real

type JS is val:T

Export type:JS.T

Function toJS(a:T)JS.T bitcast:JS.T(toptr.representation.toreal.bitcast:int(toptr.JS.a))

Function fromJS(a:JS.T)T val.bitcast:JS.T(toptr.intpart.casttoreal.bitcast:int(toptr.a)) 