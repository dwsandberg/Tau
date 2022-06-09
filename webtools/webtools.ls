Module webtools

use UTF8

use file

use inputoutput

use main2

use standard

use tools$EP

use webIO

use seq.file

use testall

Function webtools int setElementValue("pageready", "page loaded")

Function myruncmd int
let cmd=getElementValue."cmd"
let out = finishentry.if first.cmd /in "testall" then
   let args =  cmd+"+tests opttests.ls +built stdlib.libinfo o=x.html"
      testall(getfiles.args,"x.html",true)
else 
let args = cmd + getElementValue."input" + "o=x.html"
  entrypoint1(args,  getfiles.args  )
let dd = setElementValue("pageready", jsUTF8.toseqbyte.out)
callevent("svg10", "load") 

Function mirror int
let x = getElementValue."hhh"
let x2 = getElementValue."peas"
let x3 = getElementValue."cars"
let x4 = getElementValue."text"
setElementValue("mhhh", x) + setElementValue("mpeas", x2)
+ setElementValue("mcars", x3)
+ setElementValue("mtext", x4)





