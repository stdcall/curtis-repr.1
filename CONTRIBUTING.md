# Source conventions

The main file includes ordinary Typst chapter and section files.
Chapters use Arabic numbers; the Introduction is unnumbered. The 37
sections run continuously across the Introduction and Chapters 1–4.
Lettered subsections are native level-three headings.

Statements and displayed equations share the series `(section.item)`.
The exceptional series beginning at 5.0 and 36.0 use `#item-series(start: 0)`
after its section heading. The native counter still counts every object;
the section offset resets at the next heading. Inserted lettered statements
use a suffix helper with a native reference to their base object.
An author's symbolic display uses `named-equation(name: [$(ast)$])[$ … $]`
with a literal `<eq:…>` label. Its native reference prints the symbol;
the display does not advance the shared numerical series.
Exercises have their own counter within each section. Every numbered
object has a literal semantic label immediately after it; references use
native `@label` syntax. Named lemmas and theorems use the `name` argument;
unnumbered remarks use `remark(numbered: false)`, and an unnumbered example uses
`example(numbered: false)`.
Use `definitions` for an author's plural heading; it counts as one item in
the definition family.

Author hints retain their positions, including several hints within one
exercise. Its number links to the first hint; every hint links back to the
exercise. Use `exercise-heading` for a singular heading and
`exercises-heading` for a plural one.
An original footnote called more than once uses a semantic `<fn:…>` label
and native `footnote(<fn:…>)` calls. Keep every marker on its entry's page.
The label belongs to the native footnote itself. The shared note passage
stays together across statement and proof boundaries.
Footnote entries remain unbroken, including long editorial notes beside
author notes; their whole text stays on the marker's page.

Use native mathematical attachments; separate an external argument from
an index, for example `f_i lr((x))`. Lists use native `enum` items.
Layout rules belong to the common style, never to individual passages.
Ordinary statement blocks keep their introductory paragraph with the first
item of a following native list or the first displayed equation. Statements
with notes retain their native outer paragraph flow so that complete entries
stay on their marker pages.
Matrices needing cell spans or different separator strokes use the common
`block-matrix(columns, cells, hlines: (), vlines: (), delimiters: …)`.
Use native `grid.cell` spans and line records with `at` and optional `dashed`;
pass the source's delimiters explicitly.

Bibliographic descriptions are stored only in `references.bib` and
`editorial.bib`. The printing file supplies author groups, the original
year labels, and literal semantic labels. Page backlinks are computed
from mentions in the text, including notes, excluding the bibliography
itself. Index entries come only from `idx` marks next to their semantic
targets, and their page numbers are computed at build time.
Numerical citations use ordinary computed `@bib:Key` references, followed
by their external locators in prose. A descriptive caption such as `CR`
or `MO` may replace the number; never repeat a year tag by hand in a caption.

The added cover is outside printed pagination. The title, publication
leaf, dedication and blank verso occupy iii–vi; the preface begins vii.
Contents and notation continue the Roman series. Their pages reflow
freely; a counted blank verso is inserted only when needed before a new
preliminary part on an odd folio.
The half-title and its blank verso precede the Introduction; the main
text restarts at Arabic 1. Hidden folios continue the page count.

Only the book with editorial notes and its separate corrections PDF are
produced. Fonts are supplied with their licenses in `assets/fonts`.
