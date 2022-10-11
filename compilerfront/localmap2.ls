Module localmap2

use hashset.localmap2

use seq.localmap2

use set.localmap2

use standard

use symbol

use seq.symbol

Export type:localmap2

Export key(localmap2) int

Export value(localmap2) seq.symbol

Export localmap2(key:int, value:seq.symbol) localmap2

Export type:hashset.localmap2{From hashset.localmap2}

Export +(hashset.localmap2, localmap2) hashset.localmap2 {From hashset.localmap2}

Export empty:hashset.localmap2 hashset.localmap2 {From hashset.localmap2}

Export ∪(localmap2, hashset.localmap2) hashset.localmap2 {From hashset.localmap2}

Export isempty(seq.localmap2) boolean {From seq.localmap2}

Export _(seq.localmap2, int) localmap2 {From seq.localmap2}

Export isempty(set.localmap2) boolean {From set.localmap2}

Export +(set.localmap2, localmap2) set.localmap2 {From set.localmap2}

Export _(set.localmap2, int) localmap2 {From set.localmap2}

Export empty:set.localmap2 set.localmap2 {From set.localmap2}

Export ∪(localmap2, set.localmap2) set.localmap2 {From set.localmap2}

type localmap2 is key:int, value:seq.symbol

Function lookup(a:set.localmap2, key:int) set.localmap2 lookup(a, localmap2(key, empty:seq.symbol))

Function =(a:localmap2, b:localmap2) boolean key.a = key.b

Function hash(a:localmap2) int hash.key.a

Function >1(a:localmap2, b:localmap2) ordering key.a >1 key.b

Function lookup(a:hashset.localmap2, key:int) seq.localmap2
lookup(a, localmap2(key, empty:seq.symbol)) 