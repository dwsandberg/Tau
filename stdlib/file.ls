

Module file 

use standard 

use bits

use UTF8

use format


use seq.byte

use seq.filename

use seq.seq.bit

use seq.bit

Export type:file

Export fn(file) filename

Export data(file) seq.byte


Export type:filename

type filename is dirpath:seq.word,name:word,ext:word

function dir(fn:filename) word
 if length.dirpath.fn=1 then first.dirpath.fn
 else for acc="" ,p /in dirpath.fn do acc+p + "/" /for(merge(acc >> 1))

Export name(filename) word

Export ext(filename) word

Export dirpath(filename) seq.word

function filename ( dir:word,name:word,ext:word) filename
 filename([dir],name,ext)

Function fullname(fn:filename) word 
merge.if dir.fn /in "." then [name.fn,"."_1,ext.fn] else [dir.fn,"/"_1,name.fn,"."_1,ext.fn]

type file is fn:filename,xdata:seq.seq.byte,ydata:seq.seq.bit

Function data(f:file) seq.byte
 { assert ext.fn.f /nin "bc" report "bc files contain bits"+fullname.fn.f
 } for acc=empty:seq.byte,p /in xdata.f do acc+p /for(acc)
  
Function bitdata(f:file)seq.bit
  { assert ext.fn.f /nin "bc" report "only bc files contain bits"
  } for acc=empty:seq.bit,p /in ydata.f do acc+p /for(acc)

Export xdata(f:file) seq.seq.byte 

Export ydata(f:file) seq.seq.bit

Export file(fn:filename,a:seq.seq.byte,seq.seq.bit) file 




use tausupport

use seq.file

use bitstream


Function file( name:seq.word,out:seq.word) file 
   file(filename( name ),out)
  
Function file( fn:filename,out:seq.word) file {OPTION NOINLINE}
 file(  fn, if ext.fn /in "html" then 
      toseqbyte(toUTF8.htmlheader+HTMLformat.out)
      else toseqbyte.textformat.out )
   
Function file(fn:filename,a:seq.byte) file
file(  fn,toseqseqbyte.for acc = empty:bitstream, @e ∈ a do add(acc, bits.toint.@e, 8)/for(acc)
   ,empty:seq.seq.bit)

Function file(fn:filename,a:seq.bits) file
file(  fn,toseqseqbyte.tobitstream.a ,empty:seq.seq.bit)


Function filename(s:seq.word) filename  
let t=getfilenames("built",s) 
assert length.t=1 /and ext.first.t /nin "?" report "illegal file name"+s
first.t

Function getfilenames(prefix0:seq.word,s:seq.word)seq.filename
let nofile="."_1
for acc=empty:seq.filename 
, filename =  nofile
, last="?"_1
, prefix = prefix0
, suffix = "?"_1
, w ∈ s
while w /nin "=" do
 if w ∈ ".+"then next(acc, filename, w, prefix, suffix)
 else if last ∈ "." then 
   next(acc+fixfilename(prefix,filename,w),nofile, "?"_1, prefix,   w)
 else if last ∈ "+" then 
   if filename = nofile then next(acc, nofile, "?"_1, [w] , suffix)
   else next(acc+fixfilename(prefix,filename,suffix), nofile, "?"_1,  [w] , suffix)
  else if filename = nofile then next(acc, w, last, prefix, suffix)
 else next(acc+fixfilename(prefix,filename,suffix), w, last, prefix, suffix)
/for(if filename ≠ nofile /and w /nin "="  then acc + fixfilename(prefix, filename, suffix)else acc /if)

use seq.seq.char

use seq.char

use otherseq.char

function break(s:seq.char, seperators:seq.char, includeseperator:boolean)seq.seq.char
let nosep = if includeseperator then 0 else 1
let l = 
 for acc = empty:seq.int, i = 1, e ∈ s do
  next(acc + if e ∈ seperators then[i]else empty:seq.int, i + 1)
 /for(acc)
for acc = empty:seq.seq.char, i = 1, ele ∈ l + (length.s + 1)do
 next(acc + subseq(s, if i = 1 then 1 else l_(i - 1) + nosep, ele - 1), i + 1)
/for(acc)

function fixfilename(prefix:seq.word,name:word,suffix:word) filename
 {  for   acc=empty:seq.char,s /in( prefix+name) do 
     acc+decodeword.name+char1."sp"
  /for( let t=acc >> 1
  let yy=break(t,[char1."/"],false)
  for aswords="",     ss /in yy do aswords+encodeword(ss) 
  /for( filename(aswords >> 1,last.aswords,suffix))) }
  let t= decodeword.name
  let yy=break(char1."/",t)
  if length.yy=1 then
     filename(prefix,name,suffix)
  else 
   filename(encodeword(decodeword.first.prefix+char1."/"+ t >> (length.last.yy +1) )
   , encodeword(last.yy),suffix)
  
   assert dirpath.try1=dirpath.try2 /and name.try1=name.try2 report "HJKDSF"+
     dirpath.try1+name.try1+dirpath.try2+name.try2
    

Function changeext(f:filename,ext:seq.word) filename  filename(dirpath.f,name.f,first.ext)


