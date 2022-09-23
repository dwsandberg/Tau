Module webtools

use UTF8

use file

use impDependent


use standard


use webIO

use seq.file

use testall


use doc

use genLR1

use taulextable

/use enumerate

/use ParserExample

/use frontcmd

use prettycompilerfront

/use compilerfrontT.libllvm

Function tools$EP(args:seq.word, input:seq.file)seq.file  
let cmd=first.args
if cmd /in"testall"then testall(input, extractValue(args, "o"), first."noseq"∈ extractValue(args, "flags"))
else if cmd /in"usegraph"then usegraph(input, extractValue(args, "o"), extractValue(args, "include"), extractValue(args, "exclude"))
else if cmd /in"doclibrary"then doclibrary(input, extractValue(args, "o"), extractValue(args, "mods"))
else  if cmd /in"LR1"then LR1(input, extractValue(args, "o"), first."codeonly"∈ extractValue(args, "flags"), first."parameterized"∈ extractValue(args, "flags"))
else  if cmd /in"transform"then transform(input, extractValue(args, "o"), extractValue(args, "target"), extractValue(args, "modrename"), first."parseit"∈ extractValue(args, "flags"), first."reorguse"∈ extractValue(args, "flags"), first."html"∈ extractValue(args, "flags"), first."noindex"∈ extractValue(args, "flags"))
else {if cmd /in"unusedsymbols"then unusedsymbols(input, extractValue(args, "o"), extractValue(args, "flags"))
else }if cmd /in"lextable"then lextable(input, extractValue(args, "o"))
else{ if cmd /in"enumerate"then enumerate(input, extractValue(args, "o"))
else if cmd /in"sampleparser"then sampleparser(input, extractValue(args, "data"), extractValue(args, "o"))
else if cmd /in"front"then 
front(input, extractValue(args, "o"), extractValue(args, "pass"), extractValue(args, "n"), extractValue(args, "~n"), extractValue(args, "mods"), extractValue(args, "~mods"), first."within"∈ extractValue(args, "flags"), extractValue(args, "out"))
else}{ if cmd /in"testprofile"then testprofile(input, extractValue(args, "o"))
else if cmd /in"testprofile2"then testprofile2(input, extractValue(args, "o"))
else}{ assert false report "unknown command"+cmd} empty:seq.file

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

  use RI.state

Function tools$EP2(p1:jHTTP,p2:jHTTP2) int
let s=decodeZ(p1,p2) toolsX(args.s,files.s)

Function toolsX(args:seq.word,filesin:seq.file) int
let files=tools$EP(args ,filesin )
if isempty.files then final(files)
else 
let t=writefiles(files,"","finishall")  0

Function finishall(p1:jHTTP,p2:jHTTP2) int
let s=decodeZ(p1,p2)
final(files.s)

function final(files:seq.file) int
let out = UTF8.data.first.files
let dd = setElementValue("pageready", jsUTF8.toseqbyte.out)
callevent("svg10", "load") 

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

use libllvm

Module libllvm

use standard

use symbol2

Export type:libllvm

type libllvm is a:int 

Function callfunc:libllvm(ctsym:symbol, typedict:typedict, stk:seq.int)seq.int empty:seq.int

