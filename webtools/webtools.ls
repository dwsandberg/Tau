Module webtools

use UTF8

use file

use webHTTP.seq.word

use standard

use webIO

use seq.file

use subtools$root

use tests$root


use bits

use seq.byte

Function webtools int setElementValue("pageready", "page loaded")

Function myruncmd int
let input= getElementValue."input" + "o=x.html"
 let filenames=getfilenames( input << 1 )
  for acc = empty:seq.file, fn ∈ filenames do 
     acc+file(fn,empty:seq.byte)
/for(let z=readfiles(acc,input,"tools$EP2")0)

use seq.filename

  use JS.HTTPstate.seq.word

Function tools$EP2(p2:JS.HTTPstate.seq.word) int
let s=fromJS.p2 toolsX(args.s,files.s)

Function toolsX(args:seq.word,filesin:seq.file) int
let files0=subtools$EP(args ,filesin )
let files=if isempty.files0 then   tests$EP(args ,filesin ) else
  files0
if isempty.files then final(files)
else 
let t=writefiles(files,"","finishall")  0

Function finishall(p2:JS.HTTPstate.seq.word) int
final(files.fromJS( p2))

function final(files:seq.file) int
let out = UTF8.data.first.files
let dd = setElementValue("pageready", jsUTF8.toseqbyte.out)
dd

Function mycopy int
 setElementValue("input",getElementValue."cmdx")
 
Function mirror int
let x = getElementValue."hhh"
let x2 = getElementValue."peas"
let x3 = getElementValue."cars"
let x4 = getElementValue."text"
setElementValue("mhhh", x) + setElementValue("mpeas", x2)
+ setElementValue("mcars", x3)
+ setElementValue("mtext", x4)

use callconfig

Module callconfig

use standard

use symbol2

Export type:callconfig

type callconfig is a:int 

Function callfunc:callconfig(ctsym:symbol, typedict:typedict, stk:seq.int)seq.int 
if ctsym=symbol(internalmod,"+",typeint,typeint,typeint) then
 [stk_1+stk_2]
else if ctsym=symbol(internalmod,"*",typeint,typeint,typeint) then
 [stk_1 * stk_2]
else if ctsym=symbol(internalmod,"-",typeint,typeint,typeint) then
 [stk_1 - stk_2]
else if ctsym=symbol(internalmod,"/",typeint,typeint,typeint) then
 [stk_1 / stk_2]
else if ctsym=symbol(internalmod,"=",typeint,typeint,typeboolean) 
/or ctsym=symbol(internalmod,"=",typeboolean,typeboolean,typeboolean) then
 [if stk_1 = stk_2 then 1 else 0]
else 
empty:seq.int

