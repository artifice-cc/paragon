# paragon

datastructure:
- types
  - map: keys = nodes/strokes, vals = :node or :stroke
- graph
  - a digraph (from loom)
- coloring
  - map: keys = nodes/strokes, vals = :white or :black

`(forall-just jg nodes stroke)` -- creates `stroke`, creates/links each of `nodes` to it

`(exists-just jg strokes node)` -- creates `node`, creates/links each of `strokes` to it

algorithms:

`(contract jg node)` -- turns node's color to white and runs spread-white

`(expand jg node)` -- turns node's color to black and runs spread-black

TODO: Special node: :bottom (will want to avoid turning that node black)

Axioms of configuration (p 47):

-1. Everything is black or white.
0. Nothing is both black and white.
1. Everything is either a node or a stroke.
2. Nothing is both a node and a stroke.
3. Strokes send arrows only to nodes.
4. Nodes send arrows only to strokes.
5. Every stroke sends an arrow to exactly one thing.
6. Arrowing is one-way.
7. If two strokes send arrows to the same thing, and the things from which one of them receives arrows are among those from which the other receives arrows, then those strokes are identical.
8. Every node receives an arrow.

Consequences:

3a. Strokes receive arrows only from nodes.
4a. Nodes receive arrows only from strokes.

An inference pair (step) can be modeled as: `[[a1, ..., an], b]`


Axioms of coloration:

1. Every black node receives an arrow from some black inference stroke.
2. Every white node receives arrows (if any) only from white inference strokes.
3. Every black inference stroke receives arrows (if any) only from black nodes.
4. Every white inference stroke that receives an arrow receives an arrow from some white node.


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
