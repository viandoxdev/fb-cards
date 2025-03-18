//![FLASHBANG IGNORE]

#let setup(doc) = {
  set text(size: 14pt)
  set page(margin: (x: 2em, y: 1em), height: auto)
  show figure.where(kind: "Card"): it => {
    it.body
  }
  outline(target: figure)
  doc
}

#let card(id, name, tags) = {
  v(1em)
  pagebreak()
  figure(
    kind: "Card",
    supplement: [Card],
    caption: name,
    {box(
      stroke: (left: 2pt + red),
      inset: 10pt,
      fill: luma(240),
      width: 100%,
    {
      set text(size: 10pt, fill: black, weight: "bold", font: "DejaVu Sans Mono")
      set align(left)
      for path in tags {
        for tag in path.split(".") {
          tag
          if not path.ends-with(tag) {
            [ $triangle.filled.small.r$ ]
          }
        }
        linebreak()
      }
      set text(font: "", size: 16pt)
      v(-5pt)
      name
    })
  })
}
#let answer = {
  line(length: 100%, stroke: 1pt + luma(200))
}
