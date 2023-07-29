Module otherseq.T

use seq.T

use seq.seq.T

use standard

Export type:arithmeticseq.T

Export n(a:seq.T) int

Export type:seq.T {From seq.T}

Export isempty(a:seq.T) boolean {From seq.T}

Export ispseq(s:seq.T) boolean {From seq.T}

Export +(a:seq.T, b:seq.T) seq.T {From seq.T}

Export +(l:seq.T, a:T) seq.T {From seq.T}

Export <<(s:seq.T, i:int) seq.T {* removes i elements from beginning of s} {From seq.T}

Export =(a:seq.T, b:seq.T) boolean {From seq.T}

Export >>(s:seq.T, i:int) seq.T {* removes i elements from end of s} {From seq.T}

Export _(int, seq.T) T {From seq.T}

Export ^(int, s:seq.T) T

Export _(s:pseq.T, ii:int) T {From seq.T}

Export empty:seq.T seq.T {From seq.T}

Export lookup(s:seq.T, T) seq.T {From seq.T}

Export subseq(s:seq.T, start:int, finish:int) seq.T {From seq.T}

Export ∈(a:T, s:seq.T) boolean {From seq.T}

Function reverse(s:seq.T) seq.T
for acc = empty:seq.T, i = n.s while i > 0 do next(acc + i_s, i - 1),
acc

type cseq is sequence, element:T

Function _(s:cseq.T, i:int) T element.s

Function constantseq(len:int, element:T) seq.T toseq.cseq(len, element)

type cseq2 is sequence, patternlen:int, elements:seq.T

Function _(s:cseq2.T, i:int) T ((i - 1) mod patternlen.s + 1)_elements.s

Function constantseq(len:int, element:seq.T) seq.T toseq.cseq2(len, n.element, element)

Function replace(s:seq.T, index:int, value:T) seq.T
if not.ispseq.s then
 for acc = empty:seq.T, i = 1 while i < index do next(acc + i_s, i + 1)
 for oldacc = acc + value, j = index + 1 while j ≤ n.s do next(oldacc + j_s, j + 1),
 oldacc
else
 let p = to:pseq.T(s),
  if index > n.a.p then
  a.p + replace(b.p, index - n.a.p, value)
  else replace(a.p, index, value) + b.p

_____________

type arithmeticseq is sequence, step:T, start:T

unbound +(T, T) T

unbound *(int, T) T

unbound =(T, T) boolean

function _(s:arithmeticseq.T, i:int) T start.s + (i - 1) * step.s

Function arithseq(length:int, step:T, start:T) seq.T
toseq.arithmeticseq(length, step, start)

unbound >1(T, T) ordering

Function >1(a:seq.T, b:seq.T) ordering
let lengtha = n.a
let lengthb = n.b,
if lengtha > lengthb then GT else if lengtha < lengthb then LT else subcmp(a, b, 1)

function subcmp(a:seq.T, b:seq.T, i:int) ordering
if i > n.a then
EQ
else let c = i_a >1 i_b, if c = EQ then subcmp(a, b, i + 1) else c

unbound >2(T, T) ordering

Function >2(a:seq.T, b:seq.T) ordering
let lengtha = n.a
let lengthb = n.b,
if lengtha > lengthb then GT else if lengtha < lengthb then LT else subcmp2(a, b, 1)

function subcmp2(a:seq.T, b:seq.T, i:int) ordering
if i > n.a then
EQ
else let c = i_a >2 i_b, if c = EQ then subcmp2(a, b, i + 1) else c

unbound ?alpha(T, T) ordering

Function ?alpha(a:seq.T, b:seq.T) ordering subcmpalpha(a, b, 1)

function subcmpalpha(a:seq.T, b:seq.T, i:int) ordering
let lengtha = n.a
let lengthb = n.b,
if i ≤ lengtha ∧ i ≤ lengthb then
let c = ?alpha(i_a, i_b), if c = EQ then subcmpalpha(a, b, i + 1) else c
else if n.a = n.b then
EQ
else if n.a > n.b then
GT
else LT

Function sort(a:seq.T) seq.T
if n.a < 2 then
a
else merge(sort.subseq(a, 1, n.a / 2), sort.subseq(a, n.a / 2 + 1, n.a))

Function merge(a:seq.T, b:seq.T) seq.T
{* combines sorted seq}
if n.a = 0 then
b
else if n.b = 0 then
a
else if 1_b >1 (n.a)_a = GT then
a + b
else if 1_a >1 (n.b)_b = GT then
b + a
else submerge(a, b, 1, 1)

function submerge(a:seq.T, b:seq.T, i:int, j:int) seq.T
if i > n.a then
subseq(b, j, n.b)
else if j > n.b then
subseq(a, i, n.a)
else if j_b >1 i_a = LT then
[j_b] + submerge(a, b, i, j + 1)
else [i_a] + submerge(a, b, i + 1, j)

Function binarysearch(s:seq.T, val:T) int
{* binarysearch returns position in seq if found and the negation of the posistion if not found}
binarysearchNB(s, 1, n.s, val)

Function binarysearch(s:seq.T, b:int, a:int, val:T) int
assert b > 0 ∧ a ≤ n.s report "out of bounds in binary search",
binarysearchNB(s, b, a, val)

Function binarysearchNB(s:seq.T, b:int, a:int, val:T) int
if a < b then 
-(a + 1)
else
 let p = (a + b) / 2
 let c = idxNB(s, p) >1 val,
  if c = EQ then
  p
  else if c = GT then
  binarysearchNB(s, b, p - 1, val)
  else binarysearchNB(s, p + 1, a, val)

Function setinsert(s:seq.T, val:T) seq.T
{* assumes s is sorted}
let i = binarysearch(s, val),
if i > 0 then s else subseq(s, 1,-i - 1) + [val] + subseq(s,-i, n.s)

Function setdelete(s:seq.T, val:T) seq.T
{* assumes s is sorted}
let i = binarysearch(s, val),
if i > 0 then subseq(s, 1, i - 1) + subseq(s, i + 1, n.s) else s

Function setreplaceorinsert(s:seq.T, val:T) seq.T
{assumes s is sorted}
let i = binarysearch(s, val),
if i > 0 then
subseq(s, 1, i - 1) + [val] + subseq(s, i + 1, n.s)
else subseq(s, 1,-i - 1) + [val] + subseq(s,-i, n.s)

Function lpad(n:int, val:T, l:seq.T) seq.T constantseq(n - n.l, val) + l

Function break(w:T, a:seq.T) seq.seq.T break(w, empty:seq.T, a)

Function break(seperator:T, quotes:seq.T, a:seq.T) seq.seq.T
for acc = empty:seq.int, i = 1, e ∈ a
do next(acc + if e ∈ ([seperator] + quotes) then [i] else empty:seq.int, i + 1),
if isempty.acc then
[a]
else break(empty:seq.T, seperator, seperator, a, acc, 1, 1, empty:seq.seq.T)

function break(
 str:seq.T
 , currentquote:T
 , seperator:T
 , a:seq.T
 , b:seq.int
 , j:int
 , start:int
 , result:seq.seq.T
) seq.seq.T
if j > n.b then
result + (str + subseq(a, start, n.a))
else
 let i = j_b,
  if currentquote ≠ seperator then
   {in quoted string}
   if i_a = seperator then
   break(str, currentquote, seperator, a, b, j + 1, start, result)
   else if i_a = currentquote ∧ i = n.a then
   result + (str + subseq(a, start, i - 1))
   else if i_a = currentquote ∧ (i + 1)_a = currentquote then
   break(subseq(a, start, i), currentquote, seperator, a, b, j + 2, i + 2, result)
   else
    assert i_a ≠ seperator ∧ (i + 1)_a = seperator report "Format problem",
    break(
     empty:seq.T
     , seperator
     , seperator
     , a
     , b
     , j + 2
     , i + 2
     , result + (str + subseq(a, start, i - 1))
    )
  else
   {not in quoted string}
   if i_a = seperator then
   break(
    empty:seq.T
    , seperator
    , seperator
    , a
    , b
    , j + 1
    , i + 1
    , result + (str + subseq(a, start, i - 1))
   )
   else
    assert isempty(str + subseq(a, start, i - 1)) report "Format problem",
    break(str, i_a, seperator, a, b, j + 1, i + 1, result)

Function findindex(s:seq.T, w:T) int
{result > length.s when element is not found.Otherwise results is location in sequence}
for i = 1, e ∈ s while e ≠ w do i + 1,
i

________________________

unbound %(T) seq.word

Function %(term:seq.word, z:seq.T) seq.word for acc = "", i ∈ z do acc + %.i + term, acc

Function %(z:seq.T) seq.word for acc = "", i ∈ z do acc + %.i, acc

Function %n(z:seq.T) seq.word
for acc = "", idx = 1, i ∈ z do next(acc + "/br" + toword.idx + ":" + %.i, idx + 1),
acc 