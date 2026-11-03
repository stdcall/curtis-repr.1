#import "numbering.typ": numbered-record, record-number
#import "note-layout.typ": title-text

#let source(n, printed: none) = context {
  let folio = if printed != none { str(printed) } else if n <= 22 {
    numbering("i", n + 2)
  } else { str(n - 22) }
  metadata((
    kind: "source",
    file-page: n,
    printed-page: folio,
    position: here().position(),
  ))
}

#let number-text(body) = text(weight: "semibold", style: "normal", body)

// Keep a reference's invisible anchor with its first word when it wraps.
#let anchored-first(body, anchor) = {
  let body = if type(body) == str { text(body) } else { body }
  let parts = if body.has("children") { body.children } else { (body,) }
  let first = parts.position(it => (
    it.func() not in ([ ].func(), parbreak, linebreak)
  ))
  assert(first != none, message: "A reference needs visible content")
  let lead = parts.at(first)
  let sequence = [].func()
  let end = first + 1
  let punctuation = ()
  while (
    lead.has("text")
      and lead.text in ("[", "(", "{", "“", "‘")
      and end < parts.len()
      and parts.at(end).func() not in ([ ].func(), parbreak, linebreak)
  ) {
    punctuation.push(lead)
    lead = parts.at(end)
    end += 1
  }
  let anchor = anchor + sequence(punctuation)
  let gap-start = end
  while end < parts.len() and parts.at(end).func() == [ ].func() {
    end += 1
  }
  let trailing = if end > gap-start {
    text("\u{00a0}" * (end - gap-start))
  } else { [] }
  let anchored = if lead.has("text") {
    let word = lead.text.match(regex("^\\S+\\s*"))
    if word == none { box(anchor + lead + trailing) } else {
      if word.end == lead.text.len() {
        box(
          anchor + text(word.text.replace(regex("\\s"), "\u{00a0}")) + trailing,
        )
      } else {
        box(anchor + text(word.text.replace(regex("\\s"), "\u{00a0}")))
        text(lead.text.slice(word.end))
        trailing
      }
    }
  } else if lead.has("children") {
    anchored-first(lead, anchor) + trailing
  } else { box(anchor + lead + trailing) }
  sequence((..parts.slice(0, first), anchored, ..parts.slice(end)))
}

#let reference-body(it, caption) = context {
  let target = str(it.target)
  let prefix = target.split(":").first()
  let item = if it.element != none { numbered-record(it.target) }
  let unnumbered-heading = (
    item == none
      and it.element != none
      and it.element.func() == heading
      and it.element.numbering == none
  )
  let number = if item != none { record-number(item) }
  let unnumbered = item != none and item.value.kind == "unnumbered"
  let illustration = (
    prefix == "exm"
      and item != none
      and (
        item.value.at("series", default: none) == "illustration"
      )
  )
  let pending = item == none and not unnumbered-heading
  let printed = if unnumbered-heading {
    title-text(it.element.body)
  } else if pending { "?" } else if unnumbered {
    item.value.name
  } else if prefix == "case" {
    let format = item.value.at("number-format", default: "(1)")
    numbering(format.trim(".", at: end, repeat: false), ..number)
  } else if prefix == "ch" {
    numbering("1", ..number)
  } else if prefix == "bib" or illustration {
    str(number.last())
  } else if (
    prefix == "ss"
  ) {
    str(number.first()) + str(number.last())
  } else {
    number.map(str).join(".") + item.value.at("suffix", default: "")
  }
  let body = if caption { it.supplement } else if (
    unnumbered or unnumbered-heading
  ) {
    printed
  } else if (
    prefix
      in (
        "eq",
        "th",
        "lem",
        "prop",
        "cor",
        "def",
        "rem",
      )
      or (prefix == "exm" and not illustration)
  ) { [(#number-text(printed))] } else if prefix == "bib" {
    [\[#number-text(printed)\]]
  } else { number-text(printed) }
  let destination = if pending { none } else if (
    unnumbered-heading or it.element.func() == math.equation
  ) {
    it.element.location()
  } else { item.location() }
  let anchor = {
    if prefix == "bib" {
      metadata((kind: "bibliographic-mention", target: target))
    }
    metadata((
      kind: "cross-reference",
      target: target,
      resolved: not pending,
      printed: printed,
      target-location: destination,
    ))
  }
  let shown = anchored-first(body, anchor)
  if pending { shown } else {
    link(destination, if caption { shown } else { box(shown) })
  }
}

#let reference-rules(body) = {
  show ref: it => {
    let caption = it.supplement not in (auto, none, [])
    let shown = reference-body(it, caption)
    if caption { shown } else { box(shown) }
  }
  body
}

#let idx(target: none, ..path) = {
  assert(path.named().len() == 0 and path.pos().len() > 0)
  let refs(body) = {
    if body.func() == ref { (body.target,) } else if body.has("children") {
      body.children.map(refs).flatten()
    } else if body.has("body") { refs(body.body) } else { () }
  }
  let destination = if target == none { () } else { refs(target) }
  assert(
    target == none or destination.len() == 1,
    message: "An index target must contain one native reference",
  )
  let value = (kind: "index-mark", path: path.pos())
  if target != none { value.insert("target", str(destination.first())) }
  [#metadata(value)<index-mark>]
}

#let editorial-note-counter = counter("editorial-note")
#let ed-note(body) = {
  metadata((kind: "deferred-footnote", enter: true))
  editorial-note-counter.step()
  context {
    let mark = "*" + str(editorial-note-counter.get().first())
    footnote(numbering: _ => mark)[#body~— _Ed._]
    counter(footnote).update(n => n - 1)
  }
  metadata((kind: "deferred-footnote", enter: false))
}

// Native block matrices with spanning cells and independent partitions.
#let block-matrix(
  columns,
  cells,
  hlines: (),
  vlines: (),
  delimiters: (sym.brace.l, sym.brace.r),
) = {
  let stroke(line, dashed) = if line.at("dashed", default: dashed) {
    (thickness: 0.05em, dash: "dashed")
  } else { (thickness: 0.05em) }
  let matrix = grid(
    columns: columns,
    align: center + horizon,
    column-gutter: 0.5em,
    row-gutter: 0.6em,
    ..hlines.map(it => grid.hline(y: it.at, stroke: stroke(it, false))),
    ..vlines.map(it => grid.vline(x: it.at, stroke: stroke(it, true))),
    ..cells,
  )
  math.lr(delimiters.first() + matrix + delimiters.last())
}

#let Hom = math.op("Hom")
#let End = math.op("End")
#let Aut = math.op("Aut")
#let ker = math.op("ker")
#let im = math.op("im")
#let tr = math.op("tr")
#let rank = math.op("rank")
#let rad = math.op("rad")
#let Irr = math.op("Irr")
#let cf = math.op("cf")
#let char = math.op("char")
#let GL = math.upright("GL")
#let SL = math.upright("SL")
#let lmodule(ring, module) = math.attach(module, bl: ring)

// Resolve audit coordinates only in the final document query, not while a
// reference is being measured for its inline mathematical dimensions.
#let metadata-value(element) = {
  let value = element.value
  if type(value) == dictionary and "target-location" in value {
    let destination = value.remove("target-location")
    value.insert("target-position", if destination != none {
      destination.position()
    })
  }
  value
}
