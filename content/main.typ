#set document(
  title: "Methods of Representation Theory, Volume I",
  author: ("Charles W. Curtis", "Irving Reiner"),
  date: none,
)
#import "book-style.typ": book-style
#import "frontmatter/cover.typ": cover
#import "frontmatter/frontmatter-style.typ": (
  blank-leaf, notation-style, preliminary-break,
)
#import "main-defs.typ": source
#import "numbering.typ": continue-sections
#cover()
#show: book-style
#set page(numbering: "i")
#counter(page).update(3)
#page(header: none, footer: none)[#include "frontmatter/title.typ"]
#page(header: none, footer: none)[#include "frontmatter/publication.typ"]
#page(header: none, footer: none)[#include "frontmatter/dedication.typ"]
#blank-leaf()
#include "frontmatter/preface.typ"
#preliminary-break()
#heading(level: 1, numbering: none, outlined: false)[Contents]
#source(11)
#outline(title: none, depth: 3)
#preliminary-break()
#notation-style[#include "frontmatter/notation.typ"]
#preliminary-break()
#page(header: none, footer: none)[#include "frontmatter/half-title.typ"]
#blank-leaf()
#set page(numbering: "1")
#counter(page).update(1)
#include "00-00-introduction.typ"
#include "00-01-background.typ"
#include "00-02-hom-tensor.typ"
#include "00-03-semisimple.typ"
#include "00-04-dedekind.typ"
#include "00-05-radicals.typ"
#include "00-06-idempotents.typ"
#include "00-07-separable.typ"
#include "00-08-ext-tor-cohomology.typ"
#include "01-00-introduction.typ"
#continue-sections()
#include "01-09-orthogonality.typ"
#include "01-10-induced.typ"
#include "01-11-clifford-hecke.typ"
#include "01-12-tensor-algebras.typ"
#include "01-13-tensor-induction.typ"
#include "01-14-exceptional-characters.typ"
#include "01-15-artin-brauer.typ"
#include "02-00-introduction.typ"
#continue-sections()
#include "02-16-decomposition.typ"
#include "02-17-brauer-characters.typ"
#include "02-18-cartan-brauer.typ"
#include "02-19-vertices-sources.typ"
#include "02-20-green-correspondence.typ"
#include "02-21-induction-fields.typ"
#include "02-22-p-solvable.typ"
#include "03-00-introduction.typ"
#continue-sections()
#include "03-23-lattices-orders.typ"
#include "03-24-jordan-zassenhaus.typ"
#include "03-25-extensions-lattices.typ"
#include "03-26-maximal-hereditary.typ"
#include "03-27-group-rings-orders.typ"
#include "03-28-twisted-group-rings.typ"
#include "03-29-annihilator-ext.typ"
#include "04-00-introduction.typ"
#continue-sections()
#include "04-30-local-theory.typ"
#include "04-31-genus.typ"
#include "04-32-projective-lattices.typ"
#include "04-33-finite-representation-type.typ"
#include "04-34-examples-integral-representations.typ"
#include "04-35-invertible-ideals.typ"
#include "04-36-krull-schmidt.typ"
#include "04-37-bass-gorenstein.typ"
#include "80-bibliography.typ"
#include "81-editorial-bibliography.typ"
#include "90-index.typ"
