//![FLASHBANG INCLUDE]

#let ch = $"ch"$
#let sh = $"sh"$
#let gen(content) = $lr(class("opening", <) #content class("closing", >))$
#let tends(content, above: []) = $stretch(->)_script(#content)^script(#above)$
#let tendsnot(content) = math.attach($arrow.r.not$, b: math.script(content))
#let eqv(content) = math.attach($~$, b: math.script(content))
#let Ioo(a, b) = $lr(class("opening", \]) #a, #b class("closing", \[))$
#let Ico(a, b) = $lr(class("opening", \[) #a, #b class("closing", \[))$
#let Ioc(a, b) = $lr(class("opening", \]) #a, #b class("closing", \]))$
#let Icc(a, b) = $lr(class("opening", \[) #a, #b class("closing", \]))$
#let scl(a, b) = $lr(class("opening", chevron.l) #a mid(|) #b class("closing", chevron.r))$
#let dperp = $limits(plus.o)^perp$
#let func(delim: ("{", "}"), ..args) = {
  let cells = args
    .pos()
    .chunks(2)
    .enumerate() 
    .map(((i, c)) => (c.at(0), if i == 0 { sym.arrow.r } else { sym.arrow.r.bar }, c.at(1)))
  $cases(delim: delim, space display(mat(delim: #none, ..cells)))$
}
