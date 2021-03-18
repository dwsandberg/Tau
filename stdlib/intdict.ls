Module intdict.T

use standard

use seq.T

use otherseq.int

Export type:intdict.T

type intdict is keys:seq.int, data:seq.T

Export data(intdict.T)seq.T

Export keys(intdict.T)seq.int

Function empty:intdict.T intdict.T intdict(empty:seq.int, empty:seq.T)

Function add(dict:intdict.T, w:int, d:T)intdict.T
let i = binarysearch(keys.dict, w)
 if i > 0 then dict
 else
  intdict(subseq(keys.dict, 1,-i - 1) + [ w]
  + subseq(keys.dict,-i, length.keys.dict), subseq(data.dict, 1,-i - 1) + [ d]
  + subseq(data.dict,-i, length.keys.dict))

Function lookup(dict:intdict.T, w:int)seq.T
let i = binarysearch(keys.dict, w)
 if i < 0 then empty:seq.T else [(data.dict)_i]

Function replace(dict:intdict.T, w:int, d:T)intdict.T
let i = binarysearch(keys.dict, w)
 if i < 0 then
  intdict(subseq(keys.dict, 1,-i - 1) + [ w]
  + subseq(keys.dict,-i, length.keys.dict), subseq(data.dict, 1,-i - 1) + [ d]
  + subseq(data.dict,-i, length.keys.dict))
 else
  intdict(keys.dict, subseq(data.dict, 1, i - 1) + [ d]
  + subseq(data.dict, i + 1, length.keys.dict))