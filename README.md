# Tau
Experiment Programm language without assignment

This makes the state of a program easier to figure out

Only runs on Mac OS X

To get running code

move stdlib.bc to directory

cc -dynamiclib stdlib.bc  -o stdlib.dylib  -init _init22 -undefined dynamic_lookup

cc stdlib/*.c -o taumain

./taumain testall testall testall

will produce test.html file. 

A [link](./taudoc.html)