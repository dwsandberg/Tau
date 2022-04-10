Module fileIO 

use standard 

use IO2

use bits

use file

use seq.file

use format

Function finishentry( result:seq.file) UTF8 
for  acc="files created:",    f /in result do 
let discard2= createfile.f
 acc+ fullname.fn.f 
  /for( HTMLformat.acc)

Function  getfiles(rest:seq.word) seq.file 
[file(filename(rest_2, rest_3, rest_4), getfile:byte(subseq(rest, 2, 4)))]

function createfile(f:file)int createfile([fullname.fn.f], data.f)
  
function getfile(fn:filename) file file(fn,getfile:byte([fullname.fn]))
