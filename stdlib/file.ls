

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


Export type:filename

type filename is dir:word,name:word,ext:word

Export dir(filename) word

Export name(filename) word

Export ext(filename) word

Export filename ( dir:word,name:word,ext:word) filename

Function fullname(fn:filename) word 
merge.if dir.fn /in "." then [name.fn,"."_1,ext.fn] else [dir.fn,"/"_1,name.fn,"."_1,ext.fn]

type file is fn:filename,xdata:seq.seq.byte

Function data(f:file) seq.byte
  for acc=empty:seq.byte,p /in xdata.f do acc+p /for(acc)
  
Export xdata(f:file) seq.seq.byte 




use tausupport

use seq.file

use bitstream


Function file( name:seq.word,out:seq.word) file 
   file(filename( name ),out)
  
Function file( fn:filename,out:seq.word) file {OPTION NOINLINE}
 file(  fn,if ext.fn /in "sh ls txt" then  toseqbyte.textformat.out 
     else  toseqbyte.HTMLformat.out)
   
Function file(fn:filename,a:seq.byte) file
file(  fn,toseqseqbyte.for acc = empty:bitstream, @e ∈ a do add(acc, bits.toint.@e, 8)/for(acc)
   )

Function file(fn:filename,a:seq.bits) file
file(  fn,toseqseqbyte.tobitstream.a )

Export file(fn:filename,a:seq.seq.byte) file 

Function filename(s:seq.word) filename  
let t=getfilenames("built",s) 
assert length.t=1 /and ext.first.t /nin "?" report "illegal file name"+s
first.t

Function getfilenames(prefix0:seq.word,s:seq.word)seq.filename
let nofile="."_1
for acc=empty:seq.filename 
, filename =  nofile
, last="?"_1
, prefix = merge(prefix0)
, suffix = "?"_1
, w ∈ s
while w /nin "=" do
 if w ∈ ".+"then next(acc, filename, w, prefix, suffix)
 else if last ∈ "." then 
   next(acc+fixfilename(prefix,filename,w),nofile, "?"_1, prefix,   w)
 else if last ∈ "+" then 
   if filename = nofile then next(acc, nofile, "?"_1, w , suffix)
   else next(acc+fixfilename(prefix,filename,suffix), nofile, "?"_1,  w , suffix)
  else if filename = nofile then next(acc, w, last, prefix, suffix)
 else next(acc+fixfilename(prefix,filename,suffix), w, last, prefix, suffix)
/for(if filename ≠ nofile /and w /nin "="  then acc + fixfilename(prefix, filename, suffix)else acc /if)

use seq.seq.char

use seq.char

use otherseq.char

function fixfilename(prefix:word,name:word,suffix:word) filename
  let t= decodeword.name
  let yy=break(char1."/",t)
  if length.yy=1 then
     filename(prefix,name,suffix)
  else 
   filename(encodeword(decodeword.prefix+char1."/"+ t >> (length.last.yy +1) )
   , encodeword(last.yy),suffix)

Function changeext(f:filename,ext:seq.word) filename  filename(dir.f,name.f,first.ext)


