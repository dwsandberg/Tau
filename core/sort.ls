Module sort.T

use standard

use seq.T

use set.T

unbound >1(T, T) ordering

Function sort(a:seq.T) seq.T
if n.a < 2 then a
else merge(sort.subseq(a, 1, n.a / 2), sort.subseq(a, n.a / 2 + 1, n.a))

Function merge(a:seq.T, b:seq.T) seq.T
{* combines sorted seq}
let na = n.a,
if na = 0 then b
else
 let nb = n.b,
 if nb = 0 then a
 else if b sub 1 >1 a sub na = GT then a + b
 else if a sub 1 >1 b sub nb = GT then b + a
 else
  for result = empty:seq.T, i = 1, j = 1
  while i ≤ na ∧ j ≤ nb
  do
   let aval = a sub i
   {add all of b less than aval}
   for j1 = j while j1 ≤ nb ∧ b sub j1 >1 aval = LT do j1 + 1,
   if j1 > nb then next(result + subseq(b, j, j1 - 1), i, j1)
   else
    let bval = b sub j1
    {add all of a /ge bval}
    for i1 = i while i1 ≤ na ∧ bval >1 a sub i1 ≠ LT do i1 + 1,
    next(result + subseq(b, j, j1 - 1) + subseq(a, i, i1 - 1), i1, j1),
  result + subseq(a, i, na) + subseq(b, j, nb)

Function sort>3(a:seq.T) seq.T
if n.a < 2 then a
else merge>3(sort>3.subseq(a, 1, n.a / 2), sort>3.subseq(a, n.a / 2 + 1, n.a))

Function merge>3(a:seq.T, b:seq.T) seq.T
let na = n.a,
if na = 0 then b
else
 let nb = n.b,
 if nb = 0 then a
 else if b sub 1 >3 a sub na = GT then a + b
 else if a sub 1 >3 b sub nb = GT then b + a
 else
  for result = empty:seq.T, i = 1, j = 1
  while i ≤ na ∧ j ≤ nb
  do
   let aval = a sub i
   {add all of b less than aval}
   for j1 = j while j1 ≤ nb ∧ b sub j1 >3 aval = LT do j1 + 1,
   if j1 > nb then next(result + subseq(b, j, j1 - 1), i, j1)
   else
    let bval = b sub j1
    {add all of a /ge bval}
    for i1 = i while i1 ≤ na ∧ bval >3 a sub i1 ≠ LT do i1 + 1,
    next(result + subseq(b, j, j1 - 1) + subseq(a, i, i1 - 1), i1, j1),
  result + subseq(a, i, na) + subseq(b, j, nb)

unbound >3(T, T) ordering

Function sort>4(a:seq.T) seq.T
if n.a < 2 then a
else merge>4(sort>4.subseq(a, 1, n.a / 2), sort>4.subseq(a, n.a / 2 + 1, n.a))

Function merge>4(a:seq.T, b:seq.T) seq.T
let na = n.a,
if na = 0 then b
else
 let nb = n.b,
 if nb = 0 then a
 else if b sub 1 >4 a sub na = GT then a + b
 else if a sub 1 >4 b sub nb = GT then b + a
 else
  for result = empty:seq.T, i = 1, j = 1
  while i ≤ na ∧ j ≤ nb
  do
   let aval = a sub i
   {add all of b less than aval}
   for j1 = j while j1 ≤ nb ∧ b sub j1 >4 aval = LT do j1 + 1,
   if j1 > nb then next(result + subseq(b, j, j1 - 1), i, j1)
   else
    let bval = b sub j1
    {add all of a /ge bval}
    for i1 = i while i1 ≤ na ∧ bval >4 a sub i1 ≠ LT do i1 + 1,
    next(result + subseq(b, j, j1 - 1) + subseq(a, i, i1 - 1), i1, j1),
  result + subseq(a, i, na) + subseq(b, j, nb)

unbound >4(T, T) ordering

Function sort>alpha(a:seq.T) seq.T
if n.a < 2 then a
else merge>alpha(sort>alpha.subseq(a, 1, n.a / 2), sort>alpha.subseq(a, n.a / 2 + 1, n.a))

Function merge>alpha(a:seq.T, b:seq.T) seq.T
let na = n.a,
if na = 0 then b
else
 let nb = n.b,
 if nb = 0 then a
 else if b sub 1 >alpha a sub na = GT then a + b
 else if a sub 1 >alpha b sub nb = GT then b + a
 else
  for result = empty:seq.T, i = 1, j = 1
  while i ≤ na ∧ j ≤ nb
  do
   let aval = a sub i
   {add all of b less than aval}
   for j1 = j while j1 ≤ nb ∧ b sub j1 >alpha aval = LT do j1 + 1,
   if j1 > nb then next(result + subseq(b, j, j1 - 1), i, j1)
   else
    let bval = b sub j1
    {add all of a /ge bval}
    for i1 = i while i1 ≤ na ∧ bval >alpha a sub i1 ≠ LT do i1 + 1,
    next(result + subseq(b, j, j1 - 1) + subseq(a, i, i1 - 1), i1, j1),
  result + subseq(a, i, na) + subseq(b, j, nb)

unbound >alpha(T, T) ordering

Function >alpha(a:seq.T, b:seq.T) ordering subcmpalpha(a, b, 1)

function subcmpalpha(a:seq.T, b:seq.T, i:int) ordering
let lengtha = n.a
let lengthb = n.b,
if i ≤ lengtha ∧ i ≤ lengthb then
 let c = a sub i >alpha b sub i,
 if c = EQ then subcmpalpha(a, b, i + 1) else c
else if n.a = n.b then EQ
else if n.a > n.b then GT
else LT

unbound >2(T, T) ordering

Function binarysearch>2(s:seq.T, val:T) int
{* binarysearch returns position in seq if found and the negation of the posistion if not found}
binarysearch2(s, 1, n.s, val)

Function binarysearch2(s:seq.T, b:int, a:int, val:T) int
if a < b then -(a + 1)
else
 let p = (a + b) / 2
 let c = s sub p >2 val,
 if c = EQ then p
 else if c = GT then binarysearch2(s, b, p - 1, val)
 else binarysearch2(s, p + 1, a, val)

Function binarysearch>3(s:seq.T, val:T) int
{* binarysearch returns position in seq if found and the negation of the posistion if not found}
binarysearch>3(s, 1, n.s, val)

Function binarysearch>3(s:seq.T, b:int, a:int, val:T) int
if a < b then -(a + 1)
else
 let p = (a + b) / 2
 let c = s sub p >3 val,
 if c = EQ then p
 else if c = GT then binarysearch>3(s, b, p - 1, val)
 else binarysearch>3(s, p + 1, a, val)
 