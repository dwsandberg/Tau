Module constants

use real

use stdlib

Function sampleperiod int // in days 10 // 7

Function collectorarea real // 500.0 150.0 // 0.0

Function areaFloor real d1 * w1 + d1 / 2.0 * w2

function w1 real 38.0

function w2 real 16.0

function d1 real 21.0

function h1 real 14.0

Function areaWalls real(w1 + w2 + d1) * 2.0 * h1
+ // gables // d1 * d1 / 2.0
- areaWindows

function frameallowance real 7.0 / 8.0

Function areaSouthWindows real 124.0 * frameallowance

Function areaWestWindows real 17.0 * frameallowance

Function areaNorthWindows real 54.0 * frameallowance

Function areaEastWindows real 36.0 * frameallowance

Function WindowU real 0.145

Function SGHC real 0.57

Function HRVeff real 0.75

Function StoreVolume real // 700.0 // 1.0

Function StoreThermalMass real StoreVolume * WaterThermalMass

Function areaWindows real areaSouthWindows + areaWestWindows + areaNorthWindows + areaEastWindows

Function ConcreteThermalMass2 real // btu per cubic foot // 24.3

Function WaterThermalMass real 62.0

Function AirThermalMass real 0.02

Function airfilmR real 0.6

Function maxstoretemp real 140.0

Function internalheat real 1000.0

Function thermset real 70.0

Function Rgroundstore real 24.0

Function Rfloor real 48.0

Function Rstoreroom real 60.0

Function Rroof real 150.0

Function Rwall real 60.0

Function stackeffect(ventarea:real, tr:real, ta:real, height:real)real
 if ta < tr ∧ tr > 72.0 then
 0.65 * ventarea
  * sqrt(2.0 * 32.0 * height * (tr - ta) / (tr + 356.0))
  * (60.0 * 60.0 * AirThermalMass)
 else 0.0

Function venting(ventarea:real, tr:real, ta:real, height:real, windspeed:real)real
 // http:/www.level.org.nz/passive-design/ventilation/design-of-passive-ventilation/ //
 // windspeed in meters per second //
 let stackeffect = 0.65 * ventarea
 * sqrt(2.0 * 32.0 * height * (tr - ta) / (tr + 356.0))
 * (60.0 * 60.0)
 let sqft2sqmeter = 0.092903
 let Windeffect = 0.25 * ventarea * sqft2sqmeter * windspeed
 let AirFlow = if Windeffect < stackeffect then stackeffect else Windeffect
  AirFlow * (tr - ta) * AirThermalMass