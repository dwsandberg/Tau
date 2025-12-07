
Profiling  /h1

Profiling works by adding code to the procedure that tracks how much time is spent in each subprocedure
that is called. When the results are displayed, the largest time is found and normalized to 100. All
other calls are in 100th's of the largest time. 

   
// Result of run profileExample defined below. //./profileExample.html /href /a

Module profileExample

use seq.file

use file

use standard

use profile

use process.seq.word

To add profiling to the functions in this Module the follow steps were taken:
/br 1. To the function to be profiled add {OPTION PROFILE} NOINLINE was also include for these small
function since if a procedure is expaned inline, no profile results will be shown for that procedure
.
/br 2. Add a use clause   " use profile"
/br 3. Add profileresults.  " time" to make the profile results visible
/br 4. In the.bld file add to the makelib command the option profile =
/br 5. In the sources for the makelib command also+tests profile+common graphcode
/br 6. Make sure the uses option of the makelib command includes commmon. 


Function profileExample  seq.word
{OPTION PROFILE NOINLINE COMMAND /strong profile Example}
let p = process.processtest(2 sup 2 + 3)
let p2 = subtest(2 sup 2 + 3),
"test:({subtest.4+} result.p):(profileresults."time")"

function subtest(i:int) seq.word {OPTION PROFILE NOINLINE} %(i sup 10 + tr.i)

function tr(n:int) int
{OPTION PROFILE NOINLINE}
let a = %.n,
if n < 3 then n else tr(n - 1) + tr(n - 2)

function processtest(i:int) seq.word {OPTION PROFILE NOINLINE} subtest.i 