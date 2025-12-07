Module profileMeasure.T

use standard

type profileMeasure is caller:T, callee:T, measure:int

Export profileMeasure(caller:T, callee:T, measure:int) profileMeasure.T

Export caller(profileMeasure.T) T

Export callee(profileMeasure.T) T

Export measure(profileMeasure.T) int

Export type:profileMeasure.T

Function tail(a:profileMeasure.T) T caller.a

Function head(a:profileMeasure.T) T callee.a

Function reverse(a:profileMeasure.T) profileMeasure.T
profileMeasure(caller.a, caller.a, measure.a) 
