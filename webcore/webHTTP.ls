Module webHTTP.T

use JS.HTTPresult

use SpecialImports

use JS.HTTPstate.T

use bitcast.JS.HTTPstate.T

use UTF8

use bits

use seq.byte

use file

use otherseq.file

use real

use standard

use webIOtypes

use bitcast.JS.HTTPstate.seq.word

type HTTPstate is
files:seq.file
, args:T
, idx:int
, finalcall:seq.word
, method:seq.word
, funcname:seq.word

Export type:HTTPstate.T

Export files(HTTPstate.T) seq.file

Export args(HTTPstate.T) T

Export idx(HTTPstate.T) int

Export finalcall(HTTPstate.T) seq.word

Export method(HTTPstate.T) seq.word

Export HTTPstate(
files:seq.file
, args:T
, idx:int
, finalcall:seq.word
, method:seq.word
, funcname:seq.word
) HTTPstate.T

function HTTP(
name:seq.word
, header:seq.word
, body:seq.byte
, followfunc:seq.word
, state:HTTPstate.T
) real
{OPTION INLINE}
jsHTTP(
 token.name
 , jsUTF8.toseqbyte.textformat.header
 , jsUTF8.body
 , token.followfunc
 , bitcast:JS.HTTPstate.seq.word(toptr.toJS.state)
)

Function decodeZ(h2:JS.HTTPstate.T, h:JS.HTTPresult) real
let s = fromJS.h2
let newfiles =
 if between(idx.s, 1, n.files.s) then
  {update file with result ???? need to handle errors}
  let tmp = fromJS.h,
  replace(files.s, idx.s, file(fn.(idx.s)#files.s, [result.tmp], header.tmp))
 else files.s
let newstate = HTTPstate(newfiles, args.s, idx.s + 1, finalcall.s, method.s, funcname.s),
if idx.s = n.files.s then
 {all files have been processed}
 let t = HTTP("", "NONE", empty:seq.byte, finalcall.s, newstate)
 {never gets here}
 0.0
else
 let nameprefix = if method.s = "GET" then "/" else "../cgi-bin/putfile.cgi?"
 let this = (idx.newstate)#files.s
 let t = HTTP(nameprefix + fullname.fn.this, method.s, data.this, funcname.s, newstate),
 {never gets here}
 0.0

Function readarg(
files:seq.file
, args:T
, callback:seq.word
, funcname:seq.word
) JS.HTTPstate.T
toJS.HTTPstate(files, args, 0, callback, "GET", funcname)

Function writearg(
files:seq.file
, args:T
, callback:seq.word
, funcname:seq.word
) JS.HTTPstate.T
toJS.HTTPstate(files, args, 0, callback, "PUT Content-Type:application/text", funcname) 