Module bitcast.T

use ptr

type indirect is seq.T

Export type:indirect.T

Builtin indirect(T) indirect.T

Builtin fromindirect(indirect.T) T

Builtin bitcast:T(ptr) T

Builtin bitcast:T(int) T

Builtin fld:T(ptr, int) T

Builtin toptr(T) ptr 