Profiling /h1

Profiling works by adding code to the procedure that tracks how much time is spent in each called subprocedure. When the results are displayed, the largest time is found and normalized to 100. All other calls are in 100ths of the largest time. 

// Result of run profileExample defined below. //./profileExample.html /href /a

Module profileExample

use seq.file

use file

use standard

use profile

use process.seq.word

The following steps were taken to add profiling to the functions in this module. 

//ol Add //{OPTION PROFILE}./spc to the functions to be profiled. For these small functions, the option NOINLINE was included. Tf a procedure is expanded inline, no profile results will be shown for that procedure./li

Add a clause // use profile /strong /li

Add // // profileresults."time"/spc /strong to make the profile results visible /li

In the //.bld /spc file, add to the makelib command the option profile = /li

In the sources for the makelib command also+tests profile+common graphcode /li

Make sure the uses option of the makelib command includes common. /li /ol

Function profileExample seq.word
{OPTION PROFILE NOINLINE COMMAND /strong profile Example}
let p = process.processtest(2 sup 2 + 3)
let p2 = subtest(2 sup 2 + 3),
"test:({subtest.4+}result.p):(profileresults."time")"

function subtest(i:int) seq.word
{OPTION PROFILE NOINLINE}
%(i sup 10 + tr.i)

function tr(n:int) int
{OPTION PROFILE NOINLINE}
let a = %.n,
if n < 3 then n else tr(n - 1) + tr(n - 2)

function processtest(i:int) seq.word
{OPTION PROFILE NOINLINE}
subtest.i 