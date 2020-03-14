Module randomphrase

use stdlib

Function testrandomphrase seq.word if"The umber ant ambles the opal nurse" = getphrase.20 then"PASS"else"FAIL randomphrase"

Function randomphrase seq.word
let a = randomint.1
let seed = if a_1 < 0 then- a_1 + 1 else a_1
 getphrase.seed

Function getphrase(seed:int)seq.word
 let a = randomseq(seed, 6)
  "The" + adjectives_(a_1 mod 140 + 1)
  + nouns_(a_2 mod 140 + 1)
  + verbs_(a_3 mod 140 + 1)
  + "the"
  + adjectives_(a_4 mod 140 + 1)
  + nouns_(a_5 mod 140 + 1)

Function verbs seq.word"adds binds calls destroys eats fences golfs hates illustrates jumps kisses odorizes mangles nets owes plays quits registers sails takes undresses votes walks xeroxes yanks zeros ambles blows bends bombs battles brushes bubbles empties agitates aids censors circles chews dangles combs climbs dumps cycles dwindles cracks eclipses edges cuts effaces enriches zones ejects elects dips drinks dyes fights frees foils flies grows heats hobbles fails ignores aligns infects idles guards fuels imagines gains generates gives gleans issues irons knocks jilts jerks jacks jogs keeps lathers lugs lynches offers obeys meets mills occupies mocks nips mutes nags levels nurses lives notes loves pries posts pitches rolls rules phones sets rhymes races push scrapes skips sings slithers rigs snips shows splashes sows tests squirts stacks smells throws touches summons appoints swims ties travels vacums tumbles weeps wraps arouses ascends winds works whips yells"

Function nouns seq.word"ant bag cane daisy ear flower girl hat idol jam king ladder man napkin olive page queen river salt tire umbra vat walnut xray yam zoo apple bin bean brain boy bug effort empire cell chain city club cow cream editor cypress cup engine deck disk dragon duck dwarf dye echo egg elf expert face fox feast frog fur glass grave gym hog image ink igloo ale ice iron island jet arch job jig judge knob kayak kelp aunt awl lily lute lye ox outpost otter ostrich orchid onion omelet opera office ocean leaf orbit oar nymph nurse needle myth mica meat moon mug nipple noise owl pneumonia pepper phone pickle psalm python plate poetry prince puppy atom rabbit shrub sidewalk sound speaker rebel stone rock rug sun swan tomato acrobat train year wren uncle ash vole wind wench wheat wood"

Function adjectives seq.word"amber beautiful calm dim easy final gray half impure jumpy knotty large maroon navy orange part queenly red sad tall umber very warm xenox yellow zippy big acid blue alive brown bumpy charcoal cold crude drab desolate elastic enormous double fluffy egotistic full edible effective glassy eighteenth giddy heavy high hot huge ghastly germy exotic messy muddy moldy mini jelly inept little ignorant nude nosy nimble new illicit jolly jittery jagged ideal kind isolated irate gaudy ivory fancy formal feisty absurd adsorbent affordable agile airy gentle atomic annoying leaky appalling oily offensive artful oozy only opal old lowly lukewarm outdoor pearl phony pink tiny polished princely purple right raw round skinny secure short silver slimy scruffy smooth square sticky snowy soapy teary thin tumbling twin violet weak white spooky super sweet toasty triple untied plastic young average awful ruby wild wormy"