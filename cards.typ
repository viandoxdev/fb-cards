//![FLASHBANG IGNORE]

#let store = state("store", ())

#let tree() = {
  let cards_of(cards, path) = {
    let segs = path.join(".")
    cards.filter(c => segs in c.tags)
  }

  let starts_with(segs, path: ()) = {
    path.len() < segs.len() and path.zip(segs).all(((a, b)) => a == b)
  }

  let paths_children_of(cards, path) = {
    cards.map(c => c.tags)
      .flatten()
      .map(t => t.split("."))
      .filter(starts_with.with(path: path))
      .map(segs => segs.slice(0, count: path.len() + 1))
      .dedup()
  }

  let build_dict(cards, path) = {
    (
      cards: cards_of(cards, path),
      name: path.at(-1, default: none),
      children: paths_children_of(cards, path).map(p => build_dict(cards, p))
    )
  }

  let render_card(card) = {
    link(label(card.id), text(size: 9pt, card.name))
    linebreak()
  }

  let render(node) = {
    if node.name == none {
      for child in node.children {
        render(child)
      }
    } else {
      block(
        inset: (left: 0.5em, top: 0.2em, bottom: 0.2em),
        stroke: (left: 0.8pt + black),
        spacing: 0.9em,
        {
          text(weight: "bold", node.name, font: "DejaVu Sans Mono", size: 8pt)
          linebreak()
          for card in node.cards {
            render_card(card)
          }
          for child in node.children {
            render(child)
          }
        }
      )
    }
  }

  context {
    set text(size: 10pt)
    set par(leading: 6pt)
    let s = store.final()
    let d = build_dict(s, ())
    render(d)
    linebreak()
    set align(right)
    [
      #s.len() cartes.
    ]
    v(-2em)
  }
}

#let setup(doc) = {
  set text(size: 12pt)
  set page(
    margin: (x: 1em, y: 1.5em), 
    height: auto, 
    width: 250pt,
    footer: context {
      let c = store.get().len()
      let t = store.final().len()
      if c > 0 {
        set align(right)
        set text(size: 7pt)
        [
          #c / #t
        ]
      }
    }
  )
  show figure.where(kind: "Card"): it => {
    it.body
  }
  // outline(target: figure)
  tree()
  doc
}

#let card(id, name, tags) = {
  v(1em)
  pagebreak()
  store.update(s => 
    s + ((
      id: id,
      name: name,
      tags: tags,
    ),)
  )
  [#figure(
    kind: "Card",
    supplement: [Card],
    caption: name,
    {box(
      stroke: (left: 2pt + red),
      inset: 10pt,
      fill: luma(240),
      width: 100%,
    {
      {
        set text(size: 8pt, fill: black, weight: "bold", font: "DejaVu Sans Mono")
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
      }
      set text(size: 14pt, weight: "bold")
      set align(left)
      v(-5pt)
      name
    })
  }) #label(id)]
}
#let answer = {
  line(length: 100%, stroke: 1pt + luma(200))
}
