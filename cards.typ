//![FLASHBANG IGNORE]

#let store = state("store", ())
#let errors = state("errors", ())
#let had_answer = state("had_answer", (true, none))

#let signal_error(err) = {
  errors.update(errs => {
    errs.push(err)
    errs
  })
}

#let _colors = (
  text: black
)
#let _sizes = (
  text: 11pt
)

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
          for card in node.cards.sorted(key: (card) => card.name) {
            render_card(card)
          }
          for child in node.children.sorted(key: (child) => child.name) {
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
  set text(font: "Lexend")
  show math.equation: set text(font: "Noto Sans Math")
  set page(
    margin: (x: 1em, top: 1.3em, bottom: 2.3em), 
    height: auto, 
    width: 200pt,
    footer: context {
      let c = store.get().len()
      let t = store.final().len()
      if c > 0 {
        set align(right)
        set text(size: 7pt)
        v(1em)
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

  context {
    let errs = errors.get()
    let (had, last_id) = had_answer.get()
    if not had {
      errs.push("Card '" + last_id + "' doesn't have an answer.")
    }

    if errs.len() > 0 {
      pagebreak()
      for err in errs {
        box(fill: red, radius: 5pt, width: 100%, pad(rest: 10pt, {
            err
        }))
      }
    }
  }
}

#let card(rid, name, tags) = {
  had_answer.update(((had, prev_id)) => {
    if not had {
      signal_error("Card '" + prev_id + "' doesn't have an answer.")
    }
    (false, rid)
  })    

  v(1em)
  pagebreak()
  context {
    let s = store.get()
    let id = rid
    if s.find(v => v.id == rid) != none {
      signal_error("Duplicate card id '" + id + "'")
      let n = 1
      while s.find(v => v.id == rid + str(n)) != none {
        n += 1
      }
      id = rid + str(n)
    }
    store.update(s =>
      return s + ((
        id: id,
        name: name,
        tags: tags,
      ),))
    [#figure(
      kind: "Card",
      supplement: [Card],
      caption: name,
      {box(
        radius: 4pt,
        inset: 10pt,
        fill: luma(240),
        width: 100%,
      {
        {
          set text(size: 8pt, fill: blue.saturate(-40%).darken(20%), weight: "bold", font: "DejaVu Sans Mono")
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
        set align(center)
        v(-5pt)
        name
      })
    }) #label(id)]
  }
}
#let answer = {
  had_answer.update(((had, prev_id)) => {
    if had {
      if prev_id == none {
        signal_error("Can't have answer without any card.")
      } else {
        signal_error("Card '" + prev_id + "' has more than one answer.")
      }
    }
    (true, prev_id)
  })    
  line(length: 100%, stroke: 1pt + luma(200))
}
