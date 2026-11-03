// Keep each continuous text run containing a footnote together before page
// layout. Preserve styled wrappers and existing label spans.
#let note-boundary(body) = if (
  type(body) == content
    and body.func() == metadata
    and type(body.value) == dictionary
    and body.value.at("kind", default: none) == "deferred-footnote"
) { body.value.enter }
#let contains-note(body) = {
  if type(body) != content { return false }
  if note-boundary(body) == true { return true }
  if body.func() == footnote { return true }
  if body.has("children") and body.children.any(contains-note) { return true }
  if body.has("child") and contains-note(body.child) { return true }
  body.has("body") and contains-note(body.body)
}
#let sequence = [].func()
// Repeated native markers identify their note by its semantic label.
#let note-keys(body) = {
  if type(body) != content { return () }
  if body.func() == footnote {
    if type(body.body) == label { return (str(body.body),) }
    if body.has("label") { return (str(body.label),) }
    return ()
  }
  if body.has("children") { return body.children.map(note-keys).flatten() }
  if body.has("child") { return note-keys(body.child) }
  if body.has("body") { return note-keys(body.body) }
  ()
}
// A kept heading and its first paragraph form one outer block. Its top
// spacing must equal the heading's own spacing, which collapses inside it.
#let heading-above(level, numbered: true) = if level == 2 and numbered {
  5mm
} else { 4mm }
// A title is repeated in running heads and the contents. Its note belongs
// only to the original heading; preserve the remaining styled title text.
#let without-notes(body) = {
  if type(body) != content or not contains-note(body) { return body }
  if body.func() == footnote { return [] }
  if body.func() == sequence {
    let kept = ()
    let depth = 0
    for child in body.children {
      let boundary = note-boundary(child)
      if boundary == true { depth += 1 } else if boundary == false {
        depth -= 1
      } else if depth == 0 { kept.push(without-notes(child)) }
    }
    assert(depth == 0, message: "Unbalanced deferred footnote markers")
    return sequence(kept)
  }
  let fields = body.fields()
  let _ = fields.remove("label", default: none)
  if body.has("child") {
    let child = fields.remove("child")
    let styles = fields.remove("styles")
    return body.func()(without-notes(child), styles, ..fields)
  }
  if body.has("body") {
    let inner = fields.remove("body")
    return body.func()(without-notes(inner), ..fields)
  }
  body
}
#let title-text(body) = {
  if body.has("text") { return body.text }
  if body.func() in ([ ].func(), linebreak) { return " " }
  if body.has("children") { return body.children.map(title-text).join() }
  if body.has("child") { return title-text(body.child) }
  if body.has("body") { return title-text(body.body) }
  panic("Unsupported content in a heading with a note: " + repr(body))
}
#let bookmark-title(it) = if (
  contains-note(it.body)
    and (it.bookmarked == true or (it.bookmarked == auto and it.outlined))
) {
  context {
    let prefix = if it.numbering == none { "" } else {
      numbering(it.numbering, ..counter(heading).at(it.location())) + " "
    }
    metadata((
      kind: "bookmark-title",
      position: it.location().position(),
      title: prefix + title-text(without-notes(it.body)),
    ))
  }
}
#let keep-note-runs(body) = {
  if body.has("label") or not contains-note(body) { return body }
  if body.func() != sequence {
    if body.has("child") {
      let fields = body.fields()
      let child = fields.remove("child")
      let styles = fields.remove("styles")
      return body.func()(keep-note-runs(child), styles, ..fields)
    }
    return body
  }
  let children = body.children
  let result = ()
  let i = 0
  let empty = [ ].func()
  let note-spans = (:)
  for (index, child) in children.enumerate() {
    for key in note-keys(child) {
      let start = note-spans.at(key, default: (index, index)).first()
      note-spans.insert(key, (start, index))
    }
  }
  let boundary(it) = {
    if it.func() == sequence { return it.children.any(boundary) }
    if it.has("child") { return boundary(it.child) }
    (
      it.func()
        in (
          parbreak,
          block,
          grid,
          table,
          figure,
          list,
          enum,
          terms,
          list.item,
          enum.item,
          terms.item,
          heading,
          pagebreak,
          colbreak,
        )
        or (it.func() == math.equation and it.block)
    )
  }
  while i < children.len() {
    let child = children.at(i)
    let grouped = false
    // A note used in adjacent statements or paragraphs has one entry.
    // Keep the complete span of its markers in the same native page flow.
    let stop = i + 1
    let extended = true
    while extended {
      extended = false
      for span in note-spans.values() {
        if span.first() >= i and span.first() < stop and span.last() >= stop {
          stop = span.last() + 1
          extended = true
        }
      }
    }
    if stop > i + 1 {
      result.push(block(breakable: false, sequence(children.slice(i, stop))))
      i = stop
      grouped = true
    }
    if (
      not grouped
        and child.func() == heading
        and child
          .fields()
          .at(
            "level",
            default: child.fields().at("depth", default: 1),
          )
          in (2, 3)
    ) {
      let start = i + 1
      while (
        start < children.len()
          and (
            children.at(start).func() in (empty, parbreak)
          )
      ) { start += 1 }
      let stop = start
      while stop < children.len() and not boundary(children.at(stop)) {
        stop += 1
      }
      if (
        contains-note(child)
          or contains-note(sequence(children.slice(start, stop)))
      ) {
        let level = child
          .fields()
          .at(
            "level",
            default: child.fields().at("depth", default: 1),
          )
        result.push(block(
          above: heading-above(
            level,
            numbered: child.fields().at("numbering", default: auto) != none,
          ),
          breakable: false,
          sequence(children.slice(i, stop)),
        ))
        i = stop
        grouped = true
      }
    }
    if not grouped and child.func() == math.equation and child.block {
      let stop = i + 1
      while stop < children.len() and not boundary(children.at(stop)) {
        stop += 1
      }
      let tail = sequence(children.slice(i + 1, stop))
      if contains-note(tail) {
        result.push(block(breakable: false, sequence(children.slice(i, stop))))
        i = stop
        grouped = true
      }
    }
    if not grouped and not boundary(child) {
      let stop = i + 1
      while stop < children.len() and not boundary(children.at(stop)) {
        stop += 1
      }
      let run = sequence(children.slice(i, stop))
      if contains-note(run) {
        result.push(block(breakable: false, run))
        i = stop
        grouped = true
      }
    }
    if not grouped {
      result.push(keep-note-runs(child))
      i += 1
    }
  }
  sequence(result)
}
