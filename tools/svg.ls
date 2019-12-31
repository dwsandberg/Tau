Module svg

use stdlib

Function svg(body:seq.word, width:int, length:int)seq.word [ EOL]+"<svg height ="+ toword.length +"width ="+ toword.width +"> <defs> <marker id = &quot markerArrow2 &quot markerWidth = &quot 13 &quot markerHeight = &quot 13 &quot refX = &quot 2 &quot refY = &quot 7 &quot orient = &quot auto &quot > <path d = &quot M8, 13 L8, 2 L2, 7 L8, 13 &quot style = &quot fill:#000000 ; &quot /> </marker> <marker id = &quot markerArrow &quot markerWidth = &quot 13 &quot markerHeight = &quot 13 &quot refX = &quot 8 &quot refY = &quot 7 &quot orient = &quot auto &quot > <path d = &quot M2, 2 L2, 13 L8, 7 L2, 2 &quot style = &quot fill:#000000 ; &quot /> </marker> </defs>"
  + body 
  +"Your browser does not support inline SVG.</svg>"

Function line(x:int, y:int, x2:int, y2:int, arrowstart:boolean, arrowend:boolean)seq.word 
   let style =(if arrowend then"marker-end:url(#markerArrow);"else"")+(if arrowstart then"marker-start:url(#markerArrow2);"else"")
    "<path d = &quot M"+ toword.x + toword.y +"L"+ toword.x2 + toword.y2 +"&quot stroke = &quot black &quot fill = &quot none &quot"
    +(if style =""then"/>"else"style = &quot"+ style +"&quot />")
    + EOL

Function text(x:int, y:int, w:seq.word)seq.word 
   if length.w = 0 
   then w 
   else"<text id = &quot"+ w_1 +"&quot x = &quot"+ toword.x +"&quot y = &quot"+ toword.y 
   +"&quot fill = &quot black &quot onclick = &quot javascript:cmd5(this)&quot >"
   + w 
   +"</text>"
   + EOL

function nodetotext(w:word)seq.word [ w]

