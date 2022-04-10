

Module file 

use standard 

use bits

use UTF8

use format


use seq.byte

use seq.filename

Export type:file

Export fn(file) filename

Export data(file) seq.byte

Export file(fn:filename,data:seq.byte) file

Export type:filename

type filename is dir:word,name:word,ext:word

Export dir(filename) word

Export name(filename) word

Export ext(filename) word

Export filename ( dir:word,name:word,ext:word) filename

Function fullname(fn:filename) word merge.[dir.fn,"/"_1,name.fn,"."_1,ext.fn]

type file is fn:filename,data:seq.byte



Function extractValue3(s:seq.word, name:seq.word)seq.word
for value = ""
, last = "="_1
, p ∈ break(s + "?=", "=", false)
do
 next(if last ∈ name then value + p >> 1 else value
 , if isempty.p then"="_1 else last.p
 )
/for(value) 

Function file( name:seq.word,out:seq.word) file 
   file(filename( name ),out)
  
Function file( fn:filename,out:seq.word) file {OPTION NOINLINE}
   file(  fn, 
     if ext.fn /in "sh ls txt" then  toseqbyte.textformat.out 
     else  toseqbyte.HTMLformat.out)

Function filename(s:seq.word) filename  
let t=getfilenames(s) 
assert length.t=1 /and ext.first.t /nin "?" report "illegal file name"+s
first.t

Function getfilenames(s:seq.word)seq.filename
let nofile="."_1
for acc=empty:seq.filename 
, filename =  nofile
, last="?"_1
, prefix = "built"_1
, suffix = "?"_1
, w ∈ s
do
 if w ∈ ".+"then next(acc, filename, w, prefix, suffix)
 else if last ∈ "." then 
   next(acc+filename(prefix,filename,w),nofile, "?"_1, prefix,   w)
 else if last ∈ "+" then 
   if filename = nofile then next(acc, nofile, "?"_1, w , suffix)
   else next(acc+filename(prefix,filename,suffix), nofile, "?"_1,  w , suffix)
  else if filename = nofile then next(acc, w, last, prefix, suffix)
 else next(acc+filename(prefix,filename,suffix), w, last, prefix, suffix)
/for(if filename ≠ nofile then acc + filename(prefix, filename, suffix)else acc /if)

     Function changeext(f:filename,ext:seq.word) filename  filename(dir.f,name.f,first.ext)


