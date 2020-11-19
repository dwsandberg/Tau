#!/usr/local/bin/tau

Module checkdataio

run checkdataio test

use checkdata

use dataio

use fileio

use process.int

use encoding.seq.int

use ioseq.encodingpair.seq.int

use seq.seq.encodingpair.seq.int

use seq.encodingpair.seq.int

use seq.seq.int

use seq.int

use real

use ioseq.rec

use process.seq.rec

use seq.rec

use stdlib

use ioseq.word

use seq.seq.word

Function test seq.word
let i = writecheckdata.testdata
 @(+, print,"", getcheckdata2)

Function writecheckdata(t:seq.rec)int
 let t2 = place(empty:seq.int, 0, [ 2]) + t
  createfile("testdata1.data", [ 0, 0] + data.t2)

Function getcheckdata seq.rec // deepcopy.// getseq2:rec(data.getfile2."checkdata/checkdata.data", 1)

Function getcheckdata2 seq.rec deepcopy.getseq2:rec(data.getfile2."testdata1.data", 1)

function +(p:place, r:rec)place
 p + checkno.r + payee.r + amount.r + deposit.r + clear.r
 + group.r

function getrecord:rec(data:seq.int, i:int)rec
 rec(getint(data, i), getseq2:word(data, i + 1), getreal(data, i + 2), getreal(data, i + 3), getseq2:word(data, i + 4), getseq2:word(data, i + 5))

Function testdata seq.rec [ rec(0,"MARKET BASK00000752433 BIDDEFORD ME", 78.85, 78.85,"2015-10-19","Food"), rec(0,"GROUPON INC 877-788-7858 IL24528546WFVDAAGS", 12.00, 12.00,"2015-10-20","Misc"), rec(0,"RH RENY INC-PORTLAND PORTLAND ME", 38.27, 38.27,"2015-10-21","Misc"), rec(0,"WAL-MART STORE-#2659 FALMOUTH ME", 8.22, 8.22,"2015-10-22","Dept"), rec(0,"TRADER JOE'S #519 QPS PORTLAND ME", 13.37, 13.37,"2015-10-24","Food"), rec(0,"WILDWOOD MEDICINE PORTLAND ME", 20.00, 20.00,"2015-10-24","Medical")]

/Function print(a:rec)seq.word"
&br, rec("+ toword.checkno.a +", &quot"+ payee.a +"&quot,"+ print(2, amount.a)+","+ print(2, deposit.a)+", &quot"+ clear.a +"&quot, &quot"+ group.a +"&quot)"