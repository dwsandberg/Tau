Module usegraph

use UTF8

use bits

use seq.byte

use file

use newsvg

use standard

use textio

use seq.arc.word

use set.arc.word

use graph.word

use set.word

Function usegraph(input:seq.file, include:seq.word, exclude:seq.word) seq.word
{COMMAND /strong usegraph graphs /em use releationship between modules in source code. 
/br
/br options: 
/br /strong exclude lists the modules to ignore in the use clauses. 
/br /strong include restricts the modules considered to those listed.
/p Examples:<* block > usegraph /sp+built core.libsrc /tag <a /sp href ="../documentation/Ex1usegraph.html" > Result /tag </a> /sp
/br > usegraph /sp+built core.libsrc exclude: seq standard /tag <a /sp href ="../documentation/Ex2usegraph.html" > Result /tag </a> /sp
/br > usegraph /sp+built core.libsrc include: UTF8 words standard textio exclude: seq standard /tag <a /sp href ="../documentation/Ex3usegraph.html" > Result /tag </a> /sp
/br > usegraph /sp+core UTF8.ls textio words standard encoding xxhash exclude = seq standard *>
/p The last two examples give the same result. The first excludes modules from consideration and the second only includes source files of modules that should be included. }
let out = drawgraph(usegraph(breakparagraph.input, 1#"mod"), asset.include, asset.exclude),
out

Function usegraph(lib:seq.seq.word, kind:word) seq.arc.word
for currentmod = 1#"?", result = empty:seq.arc.word, p ∈ lib
do
 if isempty.p then next(currentmod, result)
 else if 1#p ∈ "module Module" then next(2#p, result)
 else if 1#p ∈ "use" then
  let m = if n.p = 2 then 2#p else if kind = 1#"mod" then 2#p else merge(p << 1),
  next(
   currentmod
   , if currentmod = m ∨ currentmod ∈ "?" then result else result + arc(currentmod, m)
  )
 else next(currentmod, result),
result 