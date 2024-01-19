Module file

use UTF8

use bits

use seq.byte

use otherseq.char

use seq.seq.char

use seq.filename

use format1

use format4

use standard

use textio

use seq.seq.word

Export type:file

Export fn(file) filename

Export rawdata(file) seq.seq.byte

Export response(file) UTF8

Export file(fn:filename, rawdata:seq.seq.byte, response:UTF8) file

Export type:filename

Export dirpath(filename) word

Export ext(filename) word

Export name(filename) word

Export HTMLformat1(myinput:seq.word) UTF8 {From format1}

Export textFormat1(myinput:seq.word) UTF8 {From format1}

Function HTMLformat(s:seq.word) UTF8 HTMLformat1.s

Function textformat(s:seq.word) UTF8 textFormat4.s

type filename is dirpath:word, name:word, ext:word

Function fullname(fn:filename) word
merge(
 if dirpath.fn ∈ "." then [name.fn, 1#".", ext.fn]
 else [dirpath.fn, 1#"/", name.fn, 1#".", ext.fn]
)

type file is fn:filename, rawdata:seq.seq.byte, response:UTF8

Function data(f:file) seq.byte
for acc = empty:seq.byte, e ∈ rawdata.f do acc + e,
acc

Function file(name:seq.word, out:seq.word) file
let fns = tofilenames.name
assert not.isempty.fns report "no file name specified",
file(1#fns, out)

Function file(fn:filename, out:seq.word) file
{OPTION NOINLINE}
file(
 fn
 , if ext.fn ∈ "html" then toseqbyte(HTMLheader + HTMLformat.out)
 else toseqbyte.textformat.out
)

Function file(fn:filename) file file(fn, [empty:seq.byte], emptyUTF8)

Function file(fn:filename, a:seq.byte) file file(fn, [a], emptyUTF8)

Function file(fn:filename, a:seq.seq.byte) file file(fn, a, emptyUTF8)

Function errors(s:seq.file) seq.word
{Checks for errors after fetching files}
for acc = "", f ∈ s
do
 let errorcode = UTF8.subseq(toseqbyte.response.f, 1, 3),
 if errorcode = toUTF8.200 ∨ errorcode = toUTF8.201 then acc
 else
  acc
   + (extractValue("error:^(towords.response.f)", "error")
   + "filename:"
   + fullname.fn.f
   + "/br"),
acc >> 1

Function errors(s:seq.seq.file) seq.word
for acc = "", e ∈ s do acc + errors.e,
acc

Function filename(s:seq.word) filename
let t = tofilenames.s
assert n.t = 1 ∧ ext.1#t ∉ "?" report "illegal file name^(s + stacktrace)",
1#t

function =(a:filename, b:filename) boolean
dirpath.b = dirpath.a ∧ name.a = name.b ∧ ext.a = ext.b

Function %(a:filename) seq.word [dirpath.a, name.a, 1#".", ext.a]

Function tofilenames(s:seq.word) seq.filename
let nofile = 1#"."
for
 acc = empty:seq.filename
 , filename = nofile
 , last = 1#"?"
 , prefix = 1#"."
 , suffix = 1#"?"
 , w ∈ s + "+"
do
 if w ∈ "+" then
  let tmp = if filename = nofile then acc else acc + fixfilename(prefix, filename, suffix),
  next(tmp, nofile, w, prefix, suffix)
 else if w ∈ "." then
  if last ∈ "+" then next(acc, filename, w, 1#".", suffix)
  else next(acc, filename, w, prefix, suffix)
 else if last ∈ "." then
  next(
   if filename = nofile then acc else acc + fixfilename(prefix, filename, w)
   , nofile
   , w
   , prefix
   , w
  )
 else if last ∈ "+" then
  if filename = nofile then next(acc, nofile, 1#"?", w, suffix)
  else next(acc + fixfilename(prefix, filename, suffix), nofile, 1#"?", w, suffix)
 else if filename = nofile then next(acc, w, last, prefix, suffix)
 else next(acc + fixfilename(prefix, filename, suffix), w, last, prefix, suffix),
acc

function fixfilename(prefix:word, name:word, suffix:word) filename
let t = decodeword.name
let yy = break(char1."/", t),
if n.yy = 1 then filename(prefix, name, suffix)
else
 let dir =
  if prefix ∈ "." then encodeword(t >> (n.1^yy + 1))
  else encodeword(decodeword.prefix + char1."/" + t >> (n.1^yy + 1)),
 filename(dir, encodeword.1^yy, suffix)

Function addDefaultName(argsin:seq.word, first:word) seq.word
let args = argsin << 1
let len = n.args,
if len > 1 ∧ 2#args ∈ ":: =" ∨ len = 0 then args else %.first + ":" + args

Function changeext(f:filename, ext:seq.word) filename filename(dirpath.f, name.f, 1#ext)

Function breakparagraph(fileseq:seq.file) seq.seq.word
for acc = empty:seq.seq.word, f ∈ fileseq
do
 let new = breakparagraph.data.f,
 if isempty.new then acc else acc + fileLine.fn.f + new,
acc

Function fileLine(fn:filename) seq.word
let a = decodeword.dirpath.fn
let b =
 if subseq(a, 1, 2) = [char1.".", char1."/"] ∧ n.a > 2 then encodeword(a << 2)
 else dirpath.fn,
"#File:+^(b)^(name.fn)." + ext.fn

Function HTMLheader UTF8
{the format of the meta tag is carefully crafted to get math unicode characters to display correctly}
textformat."<!doctype html> <meta charset =^(dq."UTF-8") ><style>
/br <!--span.avoidwrap {display:inline-block ;} span.keyword {color:blue ;}
/br span.literal {color:red ;} span.comment {color:green ;}
/br span.block {padding:0px 0px 0px 0px ; margin:0px 0px 0px 20px ; display:block ;}
/br--> </style>" 