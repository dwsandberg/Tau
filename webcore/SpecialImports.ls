Module SpecialImports

This module is used to built the imports of the wasm module.

use standard

use real

use webIOtypes

use webHTTP.seq.word

use JS.HTTPstate.seq.word

Builtin clockReal real

Builtin randomfunc real

Builtin setelementvalue(name:jsbytes, text:jsbytes) real

Builtin getelementvalue(name:jsbytes) jsbytes

Builtin getattributes2(name:jsbytes, text:jsbytes) jsbytes

Builtin setattribute2(name:jsbytes, att:jsbytes, value:jsbytes) real

Builtin callevent2(name:jsbytes, text:jsbytes) real

Builtin replacesvg(id:jsbytes, xml:jsbytes) real

Builtin jsHTTP(url:jsbytes
 , method:jsbytes
 , bodydata:jsbytes
 , followfunc:jsbytes
 , state:JS.HTTPstate.seq.word) real

Builtin arcsin(real) real

Builtin arccos(real) real

Builtin sqrt(real) real

Builtin cos(real) real

Builtin tan(real) real

Builtin sin(real) real

Builtin callprocess(real, real) real

Builtin abortfunc(real) real 