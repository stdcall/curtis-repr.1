// Subject index generated from semantic marks in the text.
#import "main-defs.typ": *
#import "main-defs.typ" as book-defs
#import "numbering.typ": numbered-record

// Mathematical parts of entry names use the same notation and fonts as
// the text. Outside dollar pairs, names are ordinary literal strings.
#let index-text(value) = {
  let position = 0
  for part in value.matches(regex("\\$[^$]+\\$")) {
    value.slice(position, part.start)
    eval(part.text, mode: "markup", scope: dictionary(book-defs))
    position = part.end
  }
  value.slice(position)
}

// Alphabetical by words; a parenthetical qualifier does not count, so
// "Base (of a root system)" precedes "Base, extended" as in the book. A
// Greek letter before a hyphen does not count either: "α-string" and
// "ξ-string" stand under "string", "π-system" under "system", as printed.
#let sort-key(path) = {
  let key = lower(path.join(" "))
  key = key.replace(regex("\s*\([^)]*\)"), "")
  key = key.replace(regex("[,’'.\"]"), "")
  key = key.replace(regex("[$_^]"), "")
  let greek = key.match(regex("^(\p{Greek})-"))
  if greek == none { key } else {
    key.slice(greek.end) + " " + greek.captures.first()
  }
}

#let dashes(text) = text.split(" ").map(_ => "—").join(" ")

// The printed form of `path` after `previous` (none at the start of a
// letter group).
#let printed(path, previous) = {
  if previous == none { return path.join(", ") }
  let parts = ()
  let shared = true
  for (i, part) in path.enumerate() {
    if shared and i < previous.len() and previous.at(i) == part {
      parts.push(dashes(part))
    } else if (
      shared
        and i < previous.len()
        and part.split(" ").first() == previous.at(i).split(" ").first()
    ) {
      let words = part.split(" ")
      parts.push(("—", ..words.slice(1)).join(" "))
      shared = false
    } else {
      parts.push(part)
      shared = false
    }
  }
  parts.join(", ")
}

// The evaluator reads the metadata element's own position after layout;
// no nested context depends on the position of the generated index.
#let locator(location) = box({
  metadata((
    kind: "cross-reference",
    target: "index-mark",
    resolved: true,
    target-position: location.position(),
  ))
  let folio = counter(page).at(location)
  let pattern = location.page-numbering()
  let shown = if pattern == none { str(folio.first()) } else {
    numbering(pattern, ..folio)
  }
  link(location, box(shown))
})

#let index-entries = context {
  // Only the marks, by their label: querying all metadata would include
  // the locators this index itself adds, and the layout would not settle.
  let marks = query(<index-mark>)
  // Collect the marks of each entry; one locator per page.
  let entries = (:)
  for mark in marks {
    let destination = mark.location()
    if "target" in mark.value {
      let target = label(mark.value.target)
      let record = numbered-record(target)
      if record == none {
        metadata((
          kind: "cross-reference",
          target: mark.value.target,
          resolved: false,
          printed: "?",
          position: here().position(),
        ))
        continue
      }
      destination = record.location()
    }
    let key = mark.value.path.join("\u{1f}")
    let record = entries.at(key, default: (path: mark.value.path, at: ()))
    let number = destination.page()
    if record.at.all(l => l.page() != number) {
      record.at.push(destination)
    }
    entries.insert(key, record)
  }
  let sorted = entries.values().sorted(key: e => sort-key(e.path))
  let previous = none
  let initial = none
  for entry in sorted {
    let letter = upper(sort-key(entry.path).first())
    if letter != initial {
      if initial != none { v(0.8em, weak: true) }
      initial = letter
      previous = none
    }
    let shown = printed(entry.path, previous)
    // The first entry of a letter group begins with a capital; a Greek
    // letter keeps its case ("α-string").
    let letters = shown.clusters()
    if previous == none and letters.first().match(regex("^[a-z]$")) != none {
      shown = upper(letters.first()) + letters.slice(1).join()
    }
    block(above: 0pt, below: 0.3em, par(hanging-indent: 1.2em)[
      #index-text(shown)
      #entry.at.sorted(key: loc => loc.page()).map(locator).join([, ])
    ])
    previous = entry.path
  }
}

#let subject-index = {
  source(835)
  heading(level: 1, numbering: none)[Index]
  set par(first-line-indent: 0pt, justify: false, leading: 0.45em)
  set text(size: 9pt)
  columns(2, gutter: 8mm, index-entries)
}
