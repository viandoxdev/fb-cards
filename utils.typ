//![FLASHBANG INCLUDE]

#let gen(content) = $lr(class("opening", <) #content class("closing", >))$
#let tends(content) = math.attach($-->$, b: math.script(content))
#let tendsnot(content) = math.attach($arrow.r.not$, b: math.script(content))
#let eqv(content) = math.attach($~$, b: math.script(content))
#let Ioo(a, b) = $lr(class("opening", \]) #a, #b class("closing", \[))$
#let Ico(a, b) = $lr(class("opening", \[) #a, #b class("closing", \[))$
#let Ioc(a, b) = $lr(class("opening", \]) #a, #b class("closing", \]))$
#let Icc(a, b) = $lr(class("opening", \[) #a, #b class("closing", \]))$
