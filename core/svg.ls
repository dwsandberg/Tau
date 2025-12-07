Module svg

use seq1.int

use seq1.seq.int

use sort.seq.int

use layernode

use seq.layernode

use standard

use uniqueids

Function text(class:seq.word, id:seq.word, x:int, y:int, w:seq.word) seq.word
{ "/tag <text /sp class = /tag:(dq.class):(if id = "" then id else "id = /tag:(dq.id)")x = /tag:(dq.%.x)y = /tag:(dq.%.y)>:(w)/tag </text>"}
atts."/tag <text = class =  :(class)=:(if id = "" then id else "id = :( id)=")x = :( x)  =y =  :(y) /br
>:(w)/tag </text>"

Function svgpath(class:seq.word, id:seq.word, path:seq.word) seq.word
atts."/tag <path  = class = :( class) =:(if id = "" then id else "id = :( id)=")d =  :( path) /br />"


 "/tag <path /sp class = /tag:(dq.class):(if id = "" then id else "id = /tag:(dq.id)")d = /tag:(dq.path)/>"

Function svg(classes2:seq.seq.word, otherAttributes:seq.seq.word, body:seq.word) seq.word
for att = "", e ∈ otherAttributes
do if isempty.e then "" else att + ":(e sub 1)= /tag:(dq(e << 1))"
for
 acc = ""
 , e ∈ for acc2 = empty:seq.seq.word, e ∈ classes2 do acc2 + "" + e,
 acc2
do acc + e
let classdefs =
 atts."/tag <style = type = text/css /br > /tag <"
 + acc
 + "/tag ></style>",
 "/tag <svg /sp:(att)>:(classdefs):(body)Your browser does not support inline SVG. /tag </svg>"

Function drawscript seq.word
{Adjust beginning of paths so the start at the end of the word}
 "/tag <script> function shiftstart(arcs){let bb = document.getElementById(arcs[0]).getBBox(); arcs.forEach(function(idval, index){if(index > 0){let element = document.getElementById(idval); let d = /tag:(dq."M")+(bb.x+bb.width)+/tag:(dq.",")+(bb.y+bb.height / 2)+element.getAttribute(/tag:(dq."/nsp d")).substring(5); element.setAttribute(/tag:(dq."/nsp d"), d);}});}/tag </script>"
 + encodeword.[char.10]

/function addatt(name:seq.word,val:seq.word) seq.word
 "/sp :(name)  = :(dq)/nsp :(val):(dq)"
 
 Function  atts(s:seq.word) seq.word
 for state=0, acc="",acc2="",   w ∈ s do 
   let new = if w ∈ "/tag /sp" then
      acc2+merge("?"+w)
       else acc2+"::(state)"+w
   if state=0 ∧  w ∈ "="  then
       next(1,acc+"/sp" ,new)
   else if state=1 ∧  w ∈ "=" then
       next(2,acc+"/nsp="+dq+"/nsp",new)
   else if state=2 ∧  w ∈ "=" then
      next(1,acc+"/nsp"+dq+"/sp",new)
   else if state=2 ∧  w ∈ "/br  " then
     next(0,acc+"/nsp"+dq,new)
    else
    next(state,acc+w,new)
    assert state=0 report 
      {for txt2="", w ∈ s do
       if w ∈ "/tag /sp" then txt2+merge("?"+w)
       else txt2+w}
    "incorrect format on atts"+acc2 
    acc
  
 Function hovertext(n:int, nodex:int, nodey:int, hovertext:seq.word) seq.word
 atts."/tag <g><rect =opacity= 0.0= x=:( nodex )=y =:(nodey) = height=0.5= width=1 /br
  /tag ></rect><rect =pointer-events=none=fill=white=opacity=0.0=x=:( nodex )=y =:(nodey)
 = height=1=width=100 /br
 /tag ></rect><text =pointer-events=none=class=nodes = x=:( nodex )=y =:(nodey)
  =opacity=0.0 = x=:( nodex )=y =:(nodey)/br
   >:(hovertext)/tag </text></g>"+ encodeword.[char.10]


/Function hovertext(n:int, nodex0:int, nodey0:int, hovertext:seq.word) seq.word
if isempty.hovertext then ""
else
  "/tag <g><rect" +addatt("opacity","0.0")+addatt("x", %.nodex0 )+addatt("y",  %.nodey0 )
 +addatt(" height","0.5")+ addatt(" height","1")+" /tag ></rect><rect"
 +addatt("pointer-events"  ,"none") 
 +addatt("fill"  ,"white")
 +addatt("opacity","0.0")+addatt("x", %.nodex0 )+addatt("y",  %.nodey0 )
 +addatt(" height","1")
 +addatt("width","100") +"/tag ></rect><text" 
 +addatt("pointer-events"  ,"none")
 +addatt("class","nodes")
  +addatt("opacity","0.0")+addatt("x", %.nodex0 )+addatt("y",  %.nodey0 )
 +"tag >:(hovertext)/tag </text></g>"
 + encodeword.[char.10]

Function nodeLabel(i:int) seq.seq.word ["", %.i, ""]

Function nodeLabel(n:word) seq.seq.word ["", %.n, ""]

Function nodeLabel(n:seq.word) seq.seq.word ["", n, ""] 