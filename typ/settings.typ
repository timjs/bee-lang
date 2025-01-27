#import "helpers.typ": *

#let serif-font = "Libertinus Serif"
#let sans-font = "Libertinus Sans"
#let math-font = ("Libertinus Math", "New Computer Modern Math")

#let template(body) = {
  set text(font: serif-font)
  show math.equation: set text(font: math-font)

  set raw(syntaxes: "assets/agda.sublime-syntax", theme: "assets/black-white.tmTheme")
  show raw: text.with(font: sans-font)
  show raw.where(block: false): box.with(
    fill: luma(tw(11.5)),
    inset: (x: 3pt),
    outset: (y: 3pt),
  )
  show raw.where(block: true): block.with(
    stroke: (left: 4pt + luma(tw(11.5))),
    inset: (left: 12pt, rest: 3pt),
  )
 // correction to the right by halve stroke width
 show raw.where(block: true): move.with(dx: 2pt)

  body
}
