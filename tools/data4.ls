Module data4

run data4 test

use ioseq.data4

use process.seq.data4

use seq.data4

use dataio

use fileio

use seq.int

use point

use real

use stdlib

use timestamp

Export type:data4 internaltype

type data4 is record timestamp:timestamp, solardirect:real, solardiffuse:real, tempF:real, sunposx:real, sunposy:real, sunposz:real, windspeed:real

to get to work with new imp had to change data4 record not to use point. Testing said that the point should be flatten by the compiler out but for some reason it is not. 

Export data4(timestamp, real, real, real, real, real, real, real)data4

Export sunposx(data4)real

Export sunposy(data4)real

Export sunposz(data4)real

Export tempF(data4)real

Export solardirect(data4)real

Export solardiffuse(data4)real

Function sunpos(a:data4)point point(sunposx.a, sunposy.a, sunposz.a)

Export windspeed(data4)real

Export timestamp(d:data4)timestamp

Function test seq.word [ toword.length.getdata]

Function writedata(t:seq.data4)int
 let t2 = place(empty:seq.int, 0, [ 2]) + t
  createfile("testdata1.data", [ 0, 0] + data.t2)

Function getdata seq.data4 // deepcopy. // getseq2:data4(data.getfile2."solardataall/solardata.data", 1)

function +(p:place, r:data4)place
 p + asseconds.timestamp.r + solardirect.r + solardiffuse.r + tempF.r + sunposx.r
 + sunposy.r
 + sunposz.r
 + windspeed.r

function getrecord:data4(data:seq.int, i:int)data4
 data4(totimestamp.getint(data, i), getreal(data, i + 1), getreal(data, i + 2), getreal(data, i + 3), getreal(data, i + 4), getreal(data, i + 5), getreal(data, i + 6), getreal(data, i + 7))