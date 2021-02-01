Module svg

use standard

use seq.seq.word

Function svg(classes:seq.seq.word, body:seq.word, width:int, length:int)seq.word
 let classdefs = ' <style type ="text/css"> ' + merge."<! [ CDATA ["
 + ((for(@e ∈((for(@e ∈ classes, acc = empty:seq.seq.word)acc +" &br." + @e)), acc ="")acc + @e))
 + "]]></style>"
  " &br <svg height =" + toword.length + "width =" + toword.width
  + ' > <defs> <marker id ="markerArrow2"markerWidth ="13"markerHeight ="13"refX ="2"refY ="7"orient ="auto"> <path d ="M8, 13 L8, 2 L2, 7 L8, 13"style ="fill:#000000 ;"/> </marker> '
  + ' <marker id ="markerArrow"markerWidth ="13"markerHeight ="13"refX ="8"refY ="7"orient ="auto"> <path d ="M2, 2 L2, 13 L8, 7 L2, 2"style ="fill:#000000 ;"/> </marker> </defs> '
  + " &br"
  + classdefs
  + " &br"
  + body
  + "Your browser does not support inline SVG.</svg>"

Function line(x:int, y:int, x2:int, y2:int, arrowstart:boolean, arrowend:boolean)seq.word
 let style =(if arrowend then"marker-end:url(#markerArrow);"else"")
 + if arrowstart then"marker-start:url(#markerArrow2);"else""
  {(' <path d ="M ' + toword.x + toword.y + "L" + toword.x2
  + toword.y2
  + '"stroke ="black"fill ="none"'
  + if style = ""then"/>"else ' style ="' + style + '"/> ')
  + " &br"}

Function text(class:seq.word, x:int, y:int, w:seq.word)seq.word
 if length.w = 0 then w
 else
  '  &br <text class ="' + class_1 + '"x ="' + toword.x
  + '"y ="'
  + toword.y
  + '"> '
  + w
  + "</text>"

function nodetotext(w:word)seq.word [ w]