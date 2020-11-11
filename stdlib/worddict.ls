Module worddict.T

use seq.T

use stdlib

use otherseq.word

Export type:worddict.T  

type worddict is record keys:seq.word, data:seq.T

Function data(worddict.T)seq.T export

Function keys(worddict.T)seq.word export

Function emptyworddict:worddict.T worddict.T worddict(empty:seq.word, empty:seq.T)

Function add(dict:worddict.T, w:word, d:T)worddict.T
 let i = binarysearch(keys.dict, w)
  if i > 0 then dict
  else
   worddict(subseq(keys.dict, 1, - i - 1) + [ w]
   + subseq(keys.dict, - i, length.keys.dict), subseq(data.dict, 1, - i - 1) + [ d]
   + subseq(data.dict, - i, length.keys.dict))

Function lookup(dict:worddict.T, w:word)seq.T
 let i = binarysearch(keys.dict, w)
  if i < 0 then empty:seq.T else [(data.dict)_i]

Function replace(dict:worddict.T, w:word, d:T)worddict.T
 let i = binarysearch(keys.dict, w)
  if i < 0 then
  worddict(subseq(keys.dict, 1, - i - 1) + [ w]
   + subseq(keys.dict, - i, length.keys.dict), subseq(data.dict, 1, - i - 1) + [ d]
   + subseq(data.dict, - i, length.keys.dict))
  else
   worddict(keys.dict, subseq(data.dict, 1, i - 1) + [ d]
   + subseq(data.dict, i + 1, length.keys.dict))