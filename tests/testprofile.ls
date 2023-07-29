Module testprofile

use seq.file

use file

use standard

use profile

use process.seq.word

To add profiling to the functions in this Module the follow steps were taken:
/br 1. To the function to be profiled add {OPTION PROFILE} NOINLINE was also include for these small
function since if a procedure is expaned inline, no profile results will be shown for that procedure
.
/br 2. Add a use clause" use profile"
/br 3. Add profileresults." time" to make the profile results visible
/br 4. In the.bld file add to the makelib command the option profile =
/br 5. In the sources for the makelib command also+tests profile+subtools graphcode
/br 6. Make sure the uses option of the makelib command include commmon.

Function testprofile(input:seq.file, o:seq.word) seq.word
{OPTION PROFILE NOINLINE ENTRYPOINT /strong test profile}
let p = process.processtest(2^2 + 3)
let p2 = subtest(2^2 + 3),
"test^({subtest.4+} result.p)^(profileresults."time")"

function subtest(i:int) seq.word {OPTION PROFILE NOINLINE} %(i^10 + tr.i)

function tr(n:int) int
{OPTION PROFILE NOINLINE}
let a = %.n,
if n < 3 then n else tr(n - 1) + tr(n - 2)

function processtest(i:int) seq.word {OPTION PROFILE NOINLINE} subtest.i 