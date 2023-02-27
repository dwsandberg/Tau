Module testprofile

use seq.file

use file

use standard

use profile

use process.seq.word

Function testprofile(input:seq.file, o:seq.word) seq.file
{OPTION PROFILE NOINLINE}
 let p = process.processtest(2^2+3)    
 let p2=subtest(2^2+3)  , 
[file(o, "test" + {subtest.4 +} result.p + profileresults."time")]

function subtest(i:int) seq.word {OPTION PROFILE NOINLINE} 
%(i^10 + tr.i)

function tr(n:int) int
{OPTION PROFILE NOINLINE}
let a = %.n,
if n < 3 then n else tr(n - 1) + tr(n - 2)

function processtest(i:int) seq.word {OPTION  PROFILE NOINLINE} subtest.i 

Function subcompilelib2(allsrc:seq.seq.word, dependentlibs:seq.int,  options:seq.word) int
{OPTION PROFILE}
let libname = %.2^2
 let z=  xxxx(options, allsrc , dependentlibs),
 2^4
 
 function xxxx(options:seq.word,allsrc:seq.seq.word,dependentlibs:seq.int) seq.int
{OPTION NOINLINE}
 empty:seq.int
