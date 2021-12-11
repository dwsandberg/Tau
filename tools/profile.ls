#!/bin/sh tau stdlib tools testprofile   checkdata 

 
Module profile

use standard

use libraryModule

use seq.liblib

use symbol2

use seq.symbol

function decode(w:symbolref, l:liblib)symbol
if between(toint.w, 1, length.decoderef.l)then(decoderef.l)_(toint.w)else Lit.toint.w

function measure(arc:parc,measure:seq.word) int
if measure = "time"then clocks.arc
    else if measure = "count"then counts.arc
    else
     assert measure = "space"report"unknown profile measure"
     space.arc

use seq.labeledarc.symbol



type  arcs/max is arcs:seq.labeledarc.symbol,max:int

Function profileresults(measure:seq.word) seq.word
let a=  for acc=arcs/max(empty:seq.labeledarc.symbol,0),  lib /in loadedLibs do
            for acc0 = arcs.acc, max=max.acc,arc ∈ profiledata.lib do
                 let m =measure(arc,measure)
                 if m=0 /or m  <  max / 100 then next(acc0,max) 
                 else  
                     next(acc0+ arc(decode(caller.arc,lib),decode(callee.arc, lib),[toword.m]),max(max,m)) 
             /for(arcs/max(acc0,max) )
  /for(acc)
let b=  for acc=empty:seq.labeledarc.symbol, arc /in arcs.a do
    let m=toint.first.label.arc 
    if m < max.a / 100 then acc else
   acc+arc(tail.arc.arc,head.arc.arc, [toword(m * 100 / max.a) ]  ) 
  /for(acc) 
{ for txt="", arc /in b do
    txt+ label.arc + print.tail.arc.arc+print.head.arc.arc  +EOL
  /for(txt)
}  
  drawgraph(for acc=empty:seq.arc.symbol , arc /in b do   acc+arc.arc /for(newgraph.acc),asset.b)
   
Function generatenode(a:set.symbol)symbol   Lit.cardinality.a

 did not get error when result type of generatednode was seq.word!!!!!

Function node2text(a:symbol)seq.word [name.a]

Function nodeTitle(a:symbol) seq.word print.a

use seq.arc.symbol

use set.symbol

use svg2graph.symbol

use graph.symbol

use set.labeledarc.symbol



 



