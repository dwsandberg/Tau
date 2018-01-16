Module parse

type r1 is record preclist:seq.seq.word, input:seq.word, n:int, tr:seq.tree.word

use seq.tree.word

use seq.word

use stdlib

use tree.word

Function print(t:tree.word)seq.word 
 if nosons.t = 0 
  then [ label.t]
  else if nosons.t = 1 
  then [ label.t]+"."+ print(t_1)
  else [ label.t, openpara]+ @(seperator.",", print,"", sons.t)+ [ closepara]

function check(r:r1, w:word)r1 
 assert this.r = w report parseerror(r,"EXPECTED"+ [ w])
  advance.r

function check(r:r1, w:seq.word)r1 
 assert this.r in w report parseerror(r,"EXPECTED"+ w)
  advance.r

function wrap(label:word, r:r1)r1 r1(preclist.r, input.r, n.r, [ tree(label, tr.r)])

function +(a:r1, b:r1)r1 r1(preclist.b, input.b, n.b, tr.a + tr.b)

function this(r:r1)word input(r)_n.r

function next(r:r1)word input(r)_(n.r + 1)

build constructs new r1 and advance

function build(r:r1, s:seq.tree.word)r1 r1(preclist.r, input.r, n.r + 1, s)

function advance(r:r1)r1 build(r, tr.r)

function valid(r:r1)r1 
 assert not(this.r in"#,)]")report parseerror(r,"DID NOT EXPECTED"+ [ this.r])
  r

Function prec(w:word, preclist:seq.seq.word)int prec(w, preclist, 1)

Function defaultprec seq.seq.word 
 ["_^", 
 "", 
 "* / mod ∪ ∩", 
 "in +-∈ ∋", 
 "= < > ? ≤ ≥ ≠ >> <<", 
 "∧", 
 "∨"]

Function prec(w:word, p:seq.seq.word, i:int)int 
 if i > length.p 
  then if w ="#"_1 then length.p + 1 else 0 
  else if w in p_i then i else prec(w, p, i + 1)

----------procedures to implement expression----------

function exp(r:r1)r1 term(r, length.preclist.r)

function termlist(r:r1, p:int)r1 
 if prec(this.r, preclist.r)= p then termlist(wrap(this.r, r + term(advance.r, p - 1)), p)else r

function doublequote word encodeword.[ 34]

function term(r:r1, p:int)r1 
 if p > 0 
  then termlist(term(r, p - 1), p)
  else if this.r = openpara 
  then check(exp.advance.r, closepara)
  else if this.r ="{"_1 
  then check(exp.advance.r,"}"_1)
  else if this.r = openbracket 
  then wrap("$build"_1, check(seqlist.exp.advance.r, closebracket))
  else if this.r ="-"_1 
  then if hasdigit.next.r 
   then // minus sign in front of integer or real literal // 
    intlit([ hyphenchar], advance.advance.r, decode.next.r)
   else 
     if next.r =","_1 then // so @(-, with parse //
     build(r, [ tree.this.valid.r])
     else 
    wrap(this.r, term(advance.r, 1))
  else if this.r = doublequote 
  then wrap("$wordlist"_1, wordlist2.build(r, empty:seq.tree.word))
  else if this.r ="let"_1 
  then let def = exp.check(advance.advance.r,"="_1)
   wrap(this.r, build(r, [ tree.next.r])+ def + exp.def)
  else if this.r in"if"
  then let ifpart = check(exp.advance.r,"then"_1)
   let thenpart = check(exp.ifpart,"else"_1)
   wrap(this.r, ifpart + thenpart + exp.thenpart)
  else if this.r ="//"_1 
  then let i = findindex("//"_1, input.r, n.r + 1)
   assert i < length.input.r report parseerror(r,"expected // before end of paragraph to end comment")
   let e = term(r1(preclist.r, input.r, i + 1, empty:seq.tree.word), p)
   r1(preclist.r, input.r, n.e, [ tree("comment"_1, @(+, tree, tr.e, subseq(input.r, n.r + 1, i - 1)))])
  else if this.r in"assert"
  then let cond = exp.advance.r 
   let message = exp.check(cond,"report"_1)
   let e = exp.message 
   r1(preclist.r, input.r, n.e, [ tree(this.r, [ tr(cond)_1, tr(e)_1, tr(message)_1])])
  else if hasdigit.this.r 
  then intlit(empty:seq.int, advance.r, decode.this.r)
  else if next.r = openpara 
  then wrap(this.r, check(explist.exp.advance.advance.r, closepara))
  else if next.r ="."_1 
  then wrap(this.r, term(advance.advance.r, 1))
  else if next.r =":"_1 
  then let x = ttype.advance.advance.r 
   r1(preclist.r, input.r, n.x, [ tree.merge([ this.r]+":"+ astype(tr(x)_1))])
  else build(r, [ tree.this.valid.r])

function astype(t:tree.word)seq.word 
 if nosons.t = 0 then [ label.t]else [ label.t]+"."+ astype(t_1)

function intlit(prefix:seq.int, r:r1, s:seq.int)r1 
 if hasdigit.this.r 
  then intlit(prefix, advance.r, s + decode.this.r)
  else if this.r ="."_1 
  then reallit(prefix, advance.r, s, 0)
  else r1(preclist.r, input.r, n.r, [ tree.encodeword(prefix + subseq(s, firstnonzero(s, 1), length.s))])

function reallit(prefix:seq.int, r:r1, s:seq.int, decimalplaces:int)r1 
 if hasdigit.this.r 
  then let d = decode.this.r 
   reallit(prefix, advance.r, s + d, decimalplaces + length.d)
  else r1(preclist.r, input.r, n.r, [ tree("makereal"_1, [ tree.encodeword(prefix + subseq(s, firstnonzero(s, 1), length.s)), tree.toword.decimalplaces])])

function firstnonzero(s:seq.int, i:int)int 
 if length.s = i then i else if s_i = 48 then firstnonzero(s, i + 1)else i

function wordlist2(r:r1)r1 
 if this.r = merge("&"+"quot")
  then r + wordlist2.build(r, [ tree.doublequote])
  else if this.r = doublequote 
  then  advance.r 
  else assert n.r + 2 < length.input.r report parseerror(r,"ERROR:expected &quot before end of paragraph")
  r + wordlist2.build(r, [ tree.this.r])

function seqlist(r:r1)r1 
 if this.r = closebracket 
  then r 
  else if this.r = comma then seqlist(r + exp.advance.r)else r

function explist(r:r1)r1 
 if this.r = comma then explist(r + exp.advance.r)else r

------------------------

function newr1(s:seq.word)r1 r1(defaultprec, s +"# #", 1, empty:seq.tree.word)

function totree(r:r1)tree.word tr(r)_1

Function expression(s:seq.word)tree.word totree.exp.newr1.s

function print(r:r1)seq.word print.tree("root"_1, tr.r)

function checkend(r:r1)r1 check(r,"#"_1)

----------------------

Function parsefuncheader(text:seq.word)tree.word 
 let r = newr1.replacements.text 
  let beforeformal = advance.advance.r 
  if this.beforeformal =":"_1 
  then let returntype = tr(check(ttype.advance.beforeformal,"export"_1))_1 
   tree(this.r, [ tree(merge([ text_2]+":"+ print.returntype), [ returntype]), tree("export"_1)])
  else let paralist = if this.beforeformal = openpara 
   then check(labeltypelist.addPara.advance.beforeformal, closepara)
   else beforeformal 
  let beforedef = ttype.paralist 
  let body = if this.beforedef in"export builtin unbound"
   then tr(checkend.exp.beforedef)_1 
   else tree("omitted"_1)
  tree(this.r, [ tree(next.r, stripname.tr.paralist + tr(beforedef)_1), body]+ tr.paralist)

function parsefunc2(r:r1)tree.word 
 let beforeformal = advance.advance.r 
  if this.beforeformal =":"_1 
  then let returntype = tr(check(ttype.advance.beforeformal,"export"_1))_1 
   tree(this.r, [ tree(merge([ next.r]+":"+ print.returntype), [ returntype]), tree("export"_1)])
  else let paralist = if this.beforeformal = openpara 
   then check(labeltypelist.addPara.advance.beforeformal, closepara)
   else beforeformal 
  let beforedef = ttype.paralist 
  tree(this.r, [ tree(next.r, stripname.tr.paralist + tr(beforedef)_1), tr(checkend.exp.beforedef)_1]+ tr.paralist)

function labeltypelist(r:r1)r1 
 if this.r = comma then r + labeltypelist.addPara.advance.r else r

function addPara(r:r1)r1 
 if next.r = colon then wrap(this.r, ttype.advance.advance.r)else wrap(colon, ttype.r)

function stripname(a:seq.tree.word)seq.tree.word @(+, lastson, empty:seq.tree.word, a)

Function lastson(s:tree.word)tree.word s_nosons.s

function ttype(r:r1)r1 
 if next.r = openpara 
  then wrap(this.r, check(ttype.advance.advance.r, closepara))
  else if next.r ="."_1 then wrap(this.r, ttype.advance.advance.r)else build(r, [ tree.this.r])

--------

function structele(rx:r1, typ:tree.word)r1 
 let r = ttype.check(advance.rx, colon)
  let fldname = this.rx 
  r1(preclist.r, input.r, n.r, [ tree(fldname, if typ = tree("int"_1)then [ tr(r)_1]else [ typ, tr(r)_1])])

function elelist(r:r1, typ:tree.word)r1 
 if this.r = comma then r + elelist(structele(check(r, comma), typ), typ)else r

Function parse(text:seq.word, scope:tree.word)tree.word 
 if text_1 ="type"_1 
  then let type = if nosons.scope > 0 then tree(text_2, [ scope_1])else tree(text_2)
   let r = advance.advance.newr1.text 
   if this.r ="#"_1 
   then tree("type"_1, [ type])
   else let r2 = check(r,"is"_1)
   if this.r2 in"encoding Encoding"
   then tree(this.r2, [ type]+ tr.checkend.ttype.advance.r2)
   else assert this.r2 in"record struct sequence"report parseerror(r2,"expected struct or sequence")
   tree(if this.r2 ="record"_1 then"struct"_1 else this.r2, [ type]+ tr.checkend.elelist(structele(advance.r2, type), type))
  else if text_1 in"use Use"
  then tree(text_1, [ totree.ttype.advance.newr1.text])
  else parsefunc2.newr1.replacements.text

function replacements seq.word 
 let l ="le ≤ ge ≥ ne ≠ and ∧ or ∨ cup ∪ cap ∩ in ∈ contains ∋"
  @(+, prep.l, empty:seq.word, arithseq(length.l / 2, 2, 1))+ @(+,_.l, empty:seq.word, arithseq(length.l / 2, 2, 2))

function prep(s:seq.word, i:int)word merge("&"+ s_i)

function sub(m:seq.word, a:word)word 
 let i = findindex(a, m)
  if i > length.m / 2 then a else m_(i + length.m / 2)

function replacements(t:seq.word)seq.word @(+, sub.replacements, empty:seq.word, t)

Function parseerror(r:r1, message:seq.word)seq.word message + prettynoparse(subseq(input.r, 1, n.r), 1, 0)

Function prettynoparse(s:seq.word, i:int, lastbreak:int)seq.word 
 if i > length.s 
  then""
  else let x = s_i 
  if x ="&quot"_1 
  then let t = findindex("&quot"_1, s, i + 1)
   {"&{ literal"+ subseq(s, i, t)+"&}"+ prettynoparse(s, t + 1, lastbreak + t - i)} 
  else if x ="//"_1 
  then let t = findindex("//"_1, s, i + 1)
   {"&br &{ comment"+ subseq(s, i, t)+"&}"+ prettynoparse(s, t + 1, t - i)} 
  else if x in"if then else let assert function Function type"
  then"&br &keyword"+ x + prettynoparse(s, i + 1, 0)
  else if x in"report"
  then"&keyword"+ x + prettynoparse(s, i + 1, lastbreak + 1)
  else if lastbreak > 20 ∧ x in")]"∨ lastbreak > 40 ∧ x in","
  then [ x]+"&br"+ prettynoparse(s, i + 1, 0)
  else if lastbreak > 20 ∧ x in"["
  then"&br"+ x + prettynoparse(s, i + 1, 0)
  else [ x]+ prettynoparse(s, i + 1, lastbreak + 1)

