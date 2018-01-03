module profile

use stdlib

use constant

use seq.stat

use UTF8

use libscope

type statencoding is encoding stat

type stat is record caller:word, callee:word, count:int

function hash(s:stat)int hash.caller.s + hash.callee.s

function =(a:stat, b:stat)boolean caller.a = caller.b ∧ callee.a = callee.b

Function maxprof int 1000

Function profile(caller:word, callee:word)seq.word 
 if caller = callee ∨ caller ="noprofile"_1 ∨ name.tosyminfo.callee ="q"_1 
  then""
  else let idx = encoding.encode(stat(caller, callee, 0), statencoding)
  if idx > maxprof then""else [ toword(idx + 1)]

function stattoCconst(s:stat)seq.word 
 {"WORD"+ caller.s +"WORD"+ callee.s }

Function profilercode(lib:word)UTF8 
 let map = subseq(mapping.statencoding, 1, maxprof)
  // if length.map < 2 then""else // 
  let part1 = addconst("RECORD 4 CONST"+ addconst.@(+, stattoCconst,"RECORD"+ toword(length.map * 2 + 2)+"LIT 0"+"LIT"+ toword(length.map * 2), map)+"LIT 0 LIT 0 LIT 0")
  UTF8x("extern"+ space +"BT"+ space +"spacecount ;"+ EOL +"static"+ space +"BT"+ space +"profilestats ["+ toword(length.map + 2)+"];"+ EOL +"static"+ space +"BT"+ space +"profileclocks ["+ toword(length.map + 2)+"];"+ EOL +"static"+ space +"BT"+ space +"profilespace ["+ toword(length.map + 2)+"];"+ EOL +"static"+ space +"int"+ space +"profilerefs ["+ toword(length.map + 2)+"];"+ EOL +"static"+ space +"processinfo"+ space +"startprofile(BT"+ space +"idx, processinfo"+ space +"x){ if(profilerefs [ idx]+ + = = 0){profileclocks [ idx]-= clock(); profilespace [ idx]-= spacecount ; } return"+ space +"x ; }"+ EOL +"static"+ space +"BT"+ space +"finishprofile(BT"+ space +"idx, BT"+ space +"x){profilestats [ idx]+ + ; if(--profilerefs [ idx]= = 0){profileclocks [ idx]+ = clock(); profilespace [ idx]+ = spacecount ; } return"+ space +"x ; }"+ EOL +"BT"+ space + lib +"$profileresult(processinfo"+ space +"PD)"+"{ profilestats [ 1]="+ toword.length.map +"; profileclocks [ 1]="+ toword.length.map +"; profilespace [ 1]="+ toword.length.map +"; C"+ part1 +"[ 1]=(BT)profilestats ; C"+ part1 +"[ 2]=(BT)profileclocks ; C"+ part1 +"[ 3]=(BT)profilespace ; return"+ space +"(BT)C"+ part1 +"; }"+ EOL)

