(ns paragon.core
  (:require [loom.graph :as graph])
  (:require [loom.alg :as graphalg])
  (:require [loom.attr :as graphattr])
  (:require [loom.io :as graphio]))

(defn new-just-graph
  []
  {:types {}
   :coloring {}
   :graph (graph/digraph)})

(defn nodes
  [jg]
  (map first (filter (fn [[_ t]] (= t :node)) (seq (:types jg)))))

(defn strokes
  [jg]
  (map first (filter (fn [[_ t]] (= t :stroke)) (seq (:types jg)))))

(defn jgcolor
  [jg stroke-or-node]
  (get-in jg [:coloring stroke-or-node] :white))

(defn jgtype
  [jg stroke-or-node]
  (get-in jg [:types stroke-or-node]))

(defn believed
  "Returns black nodes."
  [jg]
  (filter (fn [n] (= :black (jgcolor jg n))) (nodes jg)))

(defn unbelieved
  "Returns white nodes."
  [jg]
  (filter (fn [n] (= :white (jgcolor jg n))) (nodes jg)))

(defn visualize
  [jg]
  (graphio/view (:graph jg) :node {:fillcolor :white :style :filled}))

(defn check-axiom-neg1
  "Everything is black or white."
  [jg]
  (every? #{:white :black} (vals (:coloring jg))))

(defn check-axiom-0
  "Nothing is both black and white.

  Axiom 0 is confirmed from the fact that :coloring is a map."
  [jg]
  true)

(defn check-axiom-1
  [jg]
  "Everything is either a node or a stroke."
  (every? #{:node :stroke} (vals (:types jg))))

(defn check-axiom-2
  "Nothing is both a node and a stroke.

  Axiom 2 is confirmed from the fact that :types is a map."
  [jg]
  true)

(defn check-axiom-3-and-4
  "Strokes send arrows only to nodes. Nodes send arrows only to strokes."
  [jg]
  (every? (fn [[start end]]
            (cond (= :stroke (jgtype jg start)) (= :node (jgtype jg end))
                  (= :node (jgtype jg start)) (= :stroke (jgtype jg end))
                  :else nil))
          (graph/edges (:graph jg))))

(defn check-axiom-5
  "Every stroke sends an arrow to exactly one thing."
  [jg]
  (every? (fn [stroke] (= 1 (count (graph/neighbors (:graph jg) stroke))))
          (strokes jg)))

(defn check-axiom-6
  "Arrowing is one-way."
  [jg]
  (graphalg/dag? (:graph jg)))

(defn check-axiom-7
  "If two strokes send arrows to the same thing, and the things from which one of them receives arrows are among those from which the other receives arrows, then those strokes are identical."
  [jg]
  (every? (fn [s] (every? (fn [s2] (= s s2))
                          ;; find strokes s2 where s2's incoming arrows are subseteq of incoming arrows of s
                          (filter (fn [s2]
                                    (every? (set (graph/incoming (:graph jg) s))
                                            (graph/incoming (:graph jg) s2)))
                                  ;; find strokes that have an arrow to the same node
                                  (filter (fn [s2] (= (first (graph/neighbors (:graph jg) s))
                                                      (first (graph/neighbors (:graph jg) s2))))
                                          (strokes jg)))))
          (strokes jg)))

(defn check-axiom-8
  "Every node receives an arrow."
  [jg]
  (every? (fn [node] (not-empty (graph/incoming (:graph jg) node)))
          (nodes jg)))

(defn check-axiom-coloration-1
  "Every black node receives an arrow from some black inference stroke."
  [jg]
  (every? (fn [node] (or (= :white (jgcolor jg node))
                         (some (fn [in] (and (= :stroke (jgtype jg in))
                                             (= :black (jgcolor jg in))))
                               (graph/incoming (:graph jg) node))))
          (nodes jg)))

(defn check-axiom-coloration-2
  "Every white node receives arrows only from white inference strokes."
  [jg]
  (every? (fn [node] (or (= :black (jgcolor jg node))
                         (every? (fn [in] (and (= :stroke (jgtype jg in))
                                               (= :white (jgcolor jg in))))
                                 (graph/incoming (:graph jg) node))))
          (nodes jg)))

(defn check-axiom-coloration-3
  "Every black inference stroke receives arrows (if any) only from black nodes."
  [jg]
  (every? (fn [stroke] (or (= :white (jgcolor jg stroke))
                           (empty? (graph/incoming (:graph jg) stroke))
                           (every? (fn [in] (and (= :node (jgtype jg in))
                                               (= :black (jgcolor jg in))))
                                   (graph/incoming (:graph jg) stroke))))
          (strokes jg)))

(defn check-axiom-coloration-4
  "Every white inference stroke that receives an arrow receives an arrow from some white node."
  [jg]
  (every? (fn [stroke] (or (= :black (jgcolor jg stroke))
                           (empty? (graph/incoming (:graph jg) stroke))
                           (some (fn [in] (and (= :node (jgtype jg in))
                                               (= :white (jgcolor jg in))))
                                 (graph/incoming (:graph jg) stroke))))
          (strokes jg)))

(defn check-axioms
  [jg]
  (and (check-axiom-neg1 jg)
       (check-axiom-0 jg)
       (check-axiom-1 jg)
       (check-axiom-2 jg)
       (check-axiom-3-and-4 jg)
       (check-axiom-5 jg)
       (check-axiom-6 jg)
       (check-axiom-7 jg)
       (check-axiom-8 jg)
       (check-axiom-coloration-1 jg)
       (check-axiom-coloration-2 jg)
       (check-axiom-coloration-3 jg)
       (check-axiom-coloration-4 jg)))

(defn check-axioms-debug
  [jg]
  (and (or (check-axiom-neg1 jg) (println "Fails Axiom -1."))
       (or (check-axiom-0 jg) (println "Fails Axiom 0."))
       (or (check-axiom-1 jg) (println "Fails Axiom 1."))
       (or (check-axiom-2 jg) (println "Fails Axiom 2."))
       (or (check-axiom-3-and-4 jg) (println "Fails Axioms 3/4."))
       (or (check-axiom-5 jg) (println "Fails Axiom 5."))
       (or (check-axiom-6 jg) (println "Fails Axiom 6."))
       (or (check-axiom-7 jg) (println "Fails Axiom 7."))
       (or (check-axiom-8 jg) (println "Fails Axiom 8."))
       (or (check-axiom-coloration-1 jg) (println "Fails Axiom of Coloration 1."))
       (or (check-axiom-coloration-2 jg) (println "Fails Axiom of Coloration 2."))
       (or (check-axiom-coloration-3 jg) (println "Fails Axiom of Coloration 3."))
       (or (check-axiom-coloration-4 jg) (println "Fails Axiom of Coloration 4."))))

(defn premise
  [jg stroke node]
  (-> jg
      (assoc-in [:types node] :node)
      (assoc-in [:types stroke] :stroke)
      (update-in [:graph] graph/add-edges [stroke node])
      (update-in [:graph] graphattr/add-attr stroke :shape :underline)))

(defn forall-just
  [jg nodes stroke]
  (reduce (fn [jg2 node] (-> jg2
                             (assoc-in [:types node] :node)
                             (update-in [:graph] graph/add-edges [node stroke])))
          (assoc-in jg [:types stroke] :stroke) nodes))

(defn exists-just
  [jg strokes node]
  (reduce (fn [jg2 stroke] (-> jg2
                             (assoc-in [:types stroke] :stroke)
                             (update-in [:graph] graphattr/add-attr stroke :shape :underline)
                             (update-in [:graph] graph/add-edges [stroke node])))
          (assoc-in jg [:types node] :node) strokes))

(defn assert-color
  [jg stroke-or-node color]
  (-> jg
      (assoc-in [:coloring stroke-or-node] color)
      (update-in [:graph] graphattr/add-attr stroke-or-node :fillcolor color)
      (update-in [:graph] graphattr/add-attr stroke-or-node :fontcolor (if (= :black color) :white :black))))

(defn spread-white
  [jg]
  (if (check-axioms jg)
    ;; nothing to do, everything checks out
    jg
    ;; something to do (inconsistent), spread white
    (if-let [bad-stroke (first (filter (fn [s] (and (= :black (jgcolor jg s))
                                                    (or (some (fn [n] (= :white (jgcolor jg n)))
                                                              (graph/incoming (:graph jg) s))
                                                        (= :white (jgcolor jg (first (graph/neighbors (:graph jg) s)))))))
                                       (strokes jg)))]
      (recur (assert-color jg bad-stroke :white))
      (if-let [bad-node (first (filter (fn [n] (and (= :black (jgcolor jg n))
                                                    (every? (fn [s] (= :white (jgcolor jg s)))
                                                            (graph/incoming (:graph jg) n))))
                                       (nodes jg)))]
        (recur (assert-color jg bad-node :white))
        ;; non-deterministic case: a stroke is white but all of its incoming nodes are black; one of those nodes must be made white
        (let [bad-node-choices (mapcat (fn [s] (let [in (graph/incoming (:graph jg) s)]
                                                 (if (every? (fn [n] (= :black (jgcolor jg n))) in)
                                                   in [])))
                                       (filter (fn [s] (= :white (jgcolor jg s))) (strokes jg)))]
          (if (not-empty bad-node-choices)
            ;; non-determinism here; just use 'first' for the moment, since we don't know what to compare
            (recur (assert-color jg (first bad-node-choices) :white))
            jg))))))

(defn spread-black
  [jg]
  (if (check-axioms jg)
    ;; nothing to do, everything checks out
    jg
    ;; something to do (inconsistent), spread black
    ;; first case: a stroke is white but has all black incoming nodes; or, it points to a black node; turn it black
    (if-let [bad-stroke (first (filter (fn [s] (and (= :white (jgcolor jg s))
                                                    (or (and (not-empty (graph/incoming (:graph jg) s))
                                                             (every? (fn [n] (= :black (jgcolor jg n)))
                                                                     (graph/incoming (:graph jg) s)))
                                                        (= :black (jgcolor jg (first (graph/neighbors (:graph jg) s)))))))
                                       (strokes jg)))]
      (recur (assert-color jg bad-stroke :black))
      ;; second case: a node is white but has all black incoming strokes; or, one of its outgoing strokes is black; turn it black
      (if-let [bad-node (first (filter (fn [n] (and (= :white (jgcolor jg n))
                                                    (or (every? (fn [s] (= :black (jgcolor jg s)))
                                                                (graph/incoming (:graph jg) n))
                                                        (some (fn [s] (= :black (jgcolor jg s))) (graph/neighbors (:graph jg) n)))))
                                       (nodes jg)))]
        (recur (assert-color jg bad-node :black))
        jg))))

(defn expand
  [jg node]
  (-> jg (assert-color node :black)
      (spread-black)))

(defn contract
  [jg node]
  (-> jg (assert-color node :white)
      (spread-white)))
