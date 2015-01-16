# paragon

Tennant, Neil. (2012). *Changes of Mind: An Essay on Rational Belief Revision*. Oxford University Press.

- [Amazon Link](http://www.amazon.com/Changes-Mind-Rational-Belief-Revision/dp/0199655758)
- [Google Books Link](http://books.google.com/books?id=ZESwoBKGxmcC&printsec=frontcover) -- Google Books previews most of Chapter 2 (assuming you initially select Chapter 2 from the TOC menu), which includes the page numbers cited below.

## API

### Construction

`(forall-just jg nodes stroke)` -- creates `stroke`, creates/links each of `nodes` to it

`(exists-just jg strokes node)` -- creates `node`, creates/links each of `strokes` to it

### Coloring

`(contract jg node)` -- turns node's color to white and runs spread-white

`(expand jg node)` -- turns node's color to black and runs spread-black

### Visualization

`(visualize jg)`


## Internal datastructure

```clojure
{
 :types {}               ;; keys = nodes/strokes, vals = :node or :stroke
 :coloring {}            ;; map: keys = nodes/strokes, vals = :white or :black
 :graph (graph/digraph)  ;; a directed acyclic graph representing arrows, from cc.artifice/loom
}
```

## Formal definition

TODO: Special node: :bottom (will want to avoid turning that node black)

### Axioms of Configuration

(p. 47)

<ul>
<li>-1. Everything is black or white.</li>
<li>0. Nothing is both black and white.</li>
<li>1. Everything is either a node or a stroke.</li>
<li>2. Nothing is both a node and a stroke.</li>
<li>3. Strokes send arrows only to nodes.</li>
<li>4. Nodes send arrows only to strokes.</li>
<li>5. Every stroke sends an arrow to exactly one thing.</li>
<li>6. Arrowing is one-way.</li>
<li>7. If two strokes send arrows to the same thing, and the things from which one of them receives arrows are among those from which the other receives arrows, then those strokes are identical.</li>
<li>8. Every node receives an arrow.</li>
</ul>

Consequences:

<ul>
<li>3a. Strokes receive arrows only from nodes.</li>
<li>4a. Nodes receive arrows only from strokes.</li>
</ul>

### Axioms of Coloration

(pp. 49-50)

<ul>
<li>1. Every black node receives an arrow from some black inference stroke.</li>
<li>2. Every white node receives arrows only from white inference strokes. *</li>
<li>3. Every black inference stroke receives arrows (if any) only from black nodes.</li>
<li>4. Every white inference stroke that receives an arrow receives an arrow from some white node.</li>
</ul>

\* p. 49, Axiom of Coloration 2: "Every white node receives arrows (if any) only from white inference strokes." --- But Axiom 8 states "Every node receives an arrow" so the "(if any)" should be dropped from Axiom of Coloration 2.

### Coloring

Contraction: changing a black to white

Spreading white:

- (White lock) Do not make anything white black.
- (Action type 1) A black node that is initial (i.e., believed outright) can be made white, and made to stand unsupported by any (black) inference stroke above it.
- (Action type 2) A black step whose (formerly black) conclusion has been made white must have its inference stroke, and at least one of its premises (nondeterminism), made white.
- (Action type 3) A black step, any one of whose premises has been made white, must have its inference stroke made white.
- (Action type 4) If the belief A has been deprived of all the justificatory support that it formerly enjoyed---that is, when every inference stroke sending an arrow to A has been made white---then A must be given up (must be made white).

Expansion: changing a white to black

Spreading black:

- (Black lock) Do not make anything black white.



## Test cases

```
(-> (new-just-graph)
    (forall-just [:b1 :b2 :b3] :stroke1)
    (exists-just [:stroke1] :a))

(-> (new-just-graph)
    (exists-just [:b1 :b2 :b3] :a))
```

## License

Copyright © 2014 Joshua Eckroth

Distributed under the Eclipse Public License either version 1.0 or (at
your option) any later version.
