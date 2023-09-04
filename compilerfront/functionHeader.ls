Module functionHeader

use PEG

use standard

Function headerTable PEGtable
maketable."S Kind any Header {str1} /action /All
 /br / Kind any Header /action /All
 /br Header (FPL) Type /action /Discard
 /br /:Type (FPL) Type /action: /Discard
 /br /:Type Type /action /Discard
 /br / Type /action /Discard
 /br * str1 ! {!} any /action /Discard
 /br FPL FP FPL' /action /Discard
 /br * FPL', FP /action /Discard
 /br FP any:Type /action /Discard
 /br / Type /action /Discard
 /br Type any.Type /action /Discard
 /br / !, !) ! (! {any /action /Discard
 /br Kind Function /action /Discard
 /br / function /action /Discard"

Function extractHeader(tbl:PEGtable, src:seq.word) seq.word
let tmp = run(tbl, src),
if 1_tmp ∈ "Failed" then tmp else tmp << 1 