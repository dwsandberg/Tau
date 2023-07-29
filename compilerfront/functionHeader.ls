Module functionHeader

use PEG

use standard

Function headerTable PEGtable
maketable."S Kind any Header {str1} /action /All /br / Kind any Header /action /All
 /br Header (FPL) Type /action /All
 /br /:Type (FPL) Type /action: /All
 /br /:Type Type /action /All
 /br / Type /action /All
 /br * str1 ! {!} any /action /All
 /br FPL FP FPL' /action /All
 /br * FPL', FP /action /Discard
 /br FP any:Type /action /All
 /br / Type /action /All
 /br Type any.Type /action /All
 /br / !, !) ! (! {any /action /1
 /br Kind Function /action Function
 /br / function /action function"

Function extractHeader(tbl:PEGtable, src:seq.word) seq.word matchPrefix(tbl, src) 