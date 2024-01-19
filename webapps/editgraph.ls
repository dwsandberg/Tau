Module editgraph

use real

use standard

use webIO

use bits

use otherseq.char

use UTF8

use graph.int

use seq.arc.int

use set.int

use otherseq.int

Each nodes of the graph are numbered uniquely. A graph named n will be represented as <* block n 2 1, 3 1, 4 3 2, 5 *> which represents the arcs <* block (1 2) (1 3) (2 4) (2 4) *> with node 5 having no arcs to it. The follow PEG Grammar defines the representation <* table
/row Graph GraphName Node Nodes'
/row * Nodes', Node
/row Node NodeNumber Predecessors
/row * Predecessors NodeNumber
/row GraphName any
/row SVGnodeid GraphName.NodeNumber *>

The object in the html page can be manipulated with function to retrive and set attribute values (setAttribute getattributes) and to set and get the contents of elements (setElementValue and getElementValue)

When the html page is loaded the below function is called

Function editgraph real
{Note that this function name match the html page name.
/br Changes the path to reflect current location of nodes. It is call when the page is initialized and when a node is being dragged to another location. It can be found in the editgraph.html source code in a java script code snippet. }
let graph = getElementValue."graph"
let name = 1#graph
let discard = setElementValue("debug", "X" + graph)
for path = "", headxy = "", nodeid ∈ graph << 1 + ","
do
 if nodeid ∈ "," then next(path, "")
 else if headxy = "" then next(path, getattributes([name, 1#".", nodeid], "x y"))
 else
  let tail = getattributes([name, 1#".", nodeid], "x y"),
  next(path + line(tail, headxy), headxy),
setAttribute("lines", "d", path)

Function nodeSelect(id0:jsbytes) real
{is called when the mouse is released to select a node. Zero, one, or two nodes can be selected. The class of the node is changed to visually indicate that it is selected. Each SVG id is three words.}
let id = towords.id0
let lastselected = getElementValue."nodesSelected"
let discard4 =
 if n.lastselected = 6 then
  setElementValue("nodesSelected", lastselected << 3 + id)
   + setAttribute(lastselected >> 3, "class", "draggable")
 else setElementValue("nodesSelected", lastselected + id),
if id ≠ lastselected << 1 then setAttribute(id, "class", "draggable selected")
else 0.0

Function addNode real
{Create a new node a the fixed location (5, 5) with then text supplied. Called when the AddNode button is pressed.}
{find unused node number}
let graph = getElementValue."graph"
let z = asset(graph << 1) \ asset.","
for newnumber = n.z + 1, nodeid = ""
while isempty.nodeid
do
 let new = toword.newnumber,
 if new ∈ z then next(newnumber + 1, nodeid)
 else next(newnumber, [1#graph, 1#".", new])
{build new node}
let nodetxt0 = getElementValue."nodeText"
let newnode = text("draggable", nodeid, 5, 5, if isempty.nodetxt0 then nodeid else nodetxt0)
{update the graph description and add the newnode to the SVG code to draw nodes}
replaceSVG("nodes", getElementValue."nodes" + newnode)
 + setElementValue("graph", graph + ",^(newnumber)")

Function addarc real
{Adds an arc between the selected nodes. Called addArc button is pressed. }
let newarc = getElementValue."nodesSelected",
if n.newarc < 2 then 0.0
else
 let newhead = 6#newarc
 let newtail = 3#newarc
 let graph = getElementValue."graph",
 for new = [1#graph], head = "", nodeno ∈ graph << 1 + ","
 do
  if nodeno ∈ "," then
   {starting a new node}
   if head = [newhead] then {Did not find new arc so add it} next(new + newtail + nodeno, "")
   else next(new + nodeno, "")
  else if head = "" then
   {This is the beginning of a node group so set head}
   next(new + nodeno, if nodeno = newhead then [nodeno] else "nomatch")
  else if nodeno = newtail then {new arc already exists} next(new + nodeno, "nomatch")
  else next(new + nodeno, head),
 setElementValue("debug", "L" + newtail + newhead + new)
  + if n.graph + 1 = n.new then 0.0
 else
  let discard = setElementValue("graph", new >> 1),
  editgraph

function line(wtail:seq.word, whead:seq.word) seq.word
let tail = point2d.wtail
let head = point2d.whead
let b = tail - head
let c = 2.0 / length.b * b,
"M^(wtail) L^(whead) l^(rotatez.-30.0 * c) L^(whead) l^(rotatez.30.0 * c)"

use set.word

use seq.char

Function text(class:seq.word, id:seq.word, x:int, y:int, w:seq.word) seq.word
{???? had to remove /tag}
"<text /sp class =^(dq.class)^(if id = "" then id else "id =^(dq.id)") x =^(dq.%.x) y =^(dq.%.y) >^(w) </text>"

function asreals(s:seq.word) seq.real
if isempty.s then empty:seq.real
else if n.s = 1 then [toreal.toint.1#s]
else
 for acc = empty:seq.real, sign = "", intpart = 1#"0", last = 1#"?", w ∈ s + "0"
 do
  if w ∈ "." then next(acc, sign, intpart, w)
  else if last ∈ "." then next(acc + makereal(sign + [intpart, last, w]), "", 1#"0", 1#"?")
  else
   let newacc = if last ∈ "?-+" then acc else acc + makereal(sign + last),
   if w ∈ "-" then next(newacc, "-", intpart, w)
   else if w ∈ "+" then next(newacc, "", intpart, w)
   else next(newacc, sign, if last ∈ "+-" then intpart else w, w),
 acc

use otherseq.real

function point2d(s:seq.word) point2d
let k = asreals.s,
point2d(1#k, 2#k)

function %(p:point2d) seq.word
let x = print(3, x.p)
let y = print(3, y.p),
(if x << 1 = ".000" then x << 1 else x) + if y << 1 = ".000" then y << 1 else y

use point2d 