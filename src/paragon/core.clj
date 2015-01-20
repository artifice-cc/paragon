(ns paragon.core
  (:require [clojure.set :as set])
  (:require [clojure.string :as str])
  (:require [loom.graph :as graph])
  (:require [loom.alg :as graphalg])
  (:require [loom.attr :as graphattr])
  (:require [loom.io :as graphio]))

(def debugging? (atom false))

(defn turn-on-debugging [] (swap! debugging? (constantly true)))

(defn turn-off-debugging [] (swap! debugging? (constantly false)))

(defn jgstr
  [stroke-or-node]
  (if (keyword? stroke-or-node) (name stroke-or-node) (str stroke-or-node)))

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

(defn bottom?
  [stroke-or-node]
  (let [s (jgstr stroke-or-node)]
    (or (= "bottom" s)
        (= "bot" (subs s 0 (min 3 (count s)))))))

(defn white?
  [jg stroke-or-node]
  (= :white (jgcolor jg stroke-or-node)))

(defn black?
  [jg stroke-or-node]
  (= :black (jgcolor jg stroke-or-node)))

(defn node?
  [jg stroke-or-node]
  (= :node (jgtype jg stroke-or-node)))

(defn stroke?
  [jg stroke-or-node]
  (= :stroke (jgtype jg stroke-or-node)))

(defn believed
  "Returns black nodes."
  [jg]
  (filter (partial black? jg) (nodes jg)))

(defn unbelieved
  "Returns white nodes."
  [jg]
  (filter (partial white? jg) (nodes jg)))

(defn jgout
  [jg stroke-or-node]
  (graph/neighbors (:graph jg) stroke-or-node))

(defn jgin
  [jg stroke-or-node]
  (graph/incoming (:graph jg) stroke-or-node))

(defn visualize
  [jg]
  (let [g (:graph jg)
        g-nodes (-> g
                    (graphattr/add-attr-to-nodes :fillcolor :black (filter #(black? jg %) (nodes jg)))
                    (graphattr/add-attr-to-nodes :fontcolor :white (filter #(black? jg %) (nodes jg))))
        g-strokes (-> g-nodes
                      (graphattr/add-attr-to-nodes :shape :plain (strokes jg))
                      (graphattr/add-attr-to-nodes :height 0.1 (strokes jg))
                      (graphattr/add-attr-to-nodes :label "&nbsp;" (strokes jg))
                      (graphattr/add-attr-to-nodes :fillcolor :black (filter #(black? jg %) (strokes jg)))
                      (graphattr/add-attr-to-nodes :fillcolor :white (filter #(white? jg %) (strokes jg))))
        g-node-labels (reduce (fn [g n] (graphattr/add-attr g n :label (jgstr n)))
                              g-strokes (nodes jg))
        g-bottom (-> g-node-labels
                     (graphattr/add-attr :bottom :label "&perp;")
                     (graphattr/add-attr :bottom :fontsize "32")
                     (graphattr/add-attr :bottom :shape :none))]
    (graphio/view g-bottom :node {:fillcolor :white :style :filled :fontname "sans"})))

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
            (cond (stroke? jg start) (node? jg end)
                  (node? jg start) (stroke? jg end)
                  :else nil))
          (graph/edges (:graph jg))))

(defn check-axiom-5
  "Every stroke sends an arrow to exactly one thing."
  [jg]
  (every? (fn [stroke] (= 1 (count (jgout jg stroke))))
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
                                    (and (not-empty (jgin jg s))
                                         (not-empty (jgin jg s2))
                                         (every? (set (jgin jg s)) (jgin jg s2))))
                                  ;; find strokes that have an arrow to the same node
                                  (filter (fn [s2] (= (first (jgout jg s))
                                                      (first (jgout jg s2))))
                                          (strokes jg)))))
          (strokes jg)))

(defn check-axiom-8
  "Every node receives an arrow."
  [jg]
  (every? (fn [node] (not-empty (jgin jg node)))
          (nodes jg)))

(defn check-axiom-coloration-1
  "Every black node receives an arrow from some black inference stroke."
  [jg]
  (every? (fn [node] (or (white? jg node)
                         (some (fn [in] (and (stroke? jg in) (black? jg in)))
                               (jgin jg node))))
          (nodes jg)))

(defn check-axiom-coloration-2
  "Every white node receives arrows only from white inference strokes."
  [jg]
  (every? (fn [node] (or (black? jg node)
                         (every? (fn [in] (and (stroke? jg in)
                                               (white? jg in)))
                                 (jgin jg node))))
          (nodes jg)))

(defn check-axiom-coloration-3
  "Every black inference stroke receives arrows (if any) only from black nodes."
  [jg]
  (every? (fn [stroke] (or (white? jg stroke)
                           (empty? (jgin jg stroke))
                           (every? (fn [n] (and (node? jg n) (black? jg n)))
                                   (jgin jg stroke))))
          (strokes jg)))

(defn check-axiom-coloration-4
  "Every white inference stroke that receives an arrow receives an arrow from some white node."
  [jg]
  (every? (fn [stroke] (or (black? jg stroke)
                           (empty? (jgin jg stroke))
                           (some (fn [in] (and (node? jg in)
                                               (white? jg in)))
                                 (jgin jg stroke))))
          (strokes jg)))
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

(defn check-axioms
  [jg]
  (if debugging?
    (check-axioms-debug jg)
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
         (check-axiom-coloration-4 jg))))

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
                             (update-in [:graph] graph/add-edges [stroke node])))
          (assoc-in jg [:types node] :node) strokes))

(defn premise
  [jg node]
  (let [stroke (format ".%s" (jgstr node))]
    (exists-just jg [stroke] node)))

(defn can-explain
  [jg explanantia explanandum]
  (assert (sequential? explanantia))
  (let [stroke (format "%s_%s" (str/join "+" (map jgstr explanantia)) (jgstr explanandum))]
    (-> (reduce (fn [jg2 explanans] (premise jg2 explanans)) jg explanantia)
        (forall-just explanantia stroke)
        (exists-just [stroke] explanandum))))

(defn assert-color
  [jg stroke-or-node color]
  (when @debugging? (println "asserting" stroke-or-node "as" color))
  (assoc-in jg [:coloring stroke-or-node] color))

(defn assert-black
  [jg stroke-or-node]
  (assert-color jg stroke-or-node :black))

(defn assert-white
  [jg stroke-or-node]
  (assert-color jg stroke-or-node :white))

(defn add-inconsistencies
  "Indicate nodes that are mutually inconsistent.

  Usage example: (add-inconsistencies jg [:node1 :node2 :node3])"
  [jg nodes]
  (let [botstroke (format "bot_%s" (str/join "-" (map jgstr nodes)))]
    (-> jg
        (forall-just nodes botstroke)
        (exists-just [botstroke] :bottom))))

(defn spread-white
  [jg]
  (if (check-axioms jg)
    ;; nothing to do, everything checks out
    (do (when @debugging? (println "All axioms satisfied in spread-white."))
        jg)
    ;; something to do (inconsistent), spread white
    (if-let [bad-stroke (first (filter (fn [s] (and (black? jg s)
                                                    (or (some (fn [n] (white? jg n))
                                                              (jgin jg s))
                                                        (white? jg (first (jgout jg s))))))
                                       (strokes jg)))]
      (recur (assert-white jg bad-stroke))
      (if-let [bad-node (first (filter (fn [n] (and (black? jg n)
                                                    (every? (fn [s] (white? jg s))
                                                            (jgin jg n))))
                                       (nodes jg)))]
        (recur (assert-white jg bad-node))
        ;; non-deterministic case: a stroke is white but all of its incoming nodes are black; one of those nodes must be made white;
        ;; just use 'first' for the moment, since we don't know what to compare
        (if-let [bad-node-choice (first (mapcat (fn [s] (let [in (jgin jg s)]
                                                          (if (every? (fn [n] (black? jg n)) in)
                                                            in [])))
                                                (filter (fn [s] (white? jg s)) (strokes jg))))]
          (recur (assert-white jg bad-node-choice))
          (do (when @debugging? (println "Axioms failed in spread-white."))
              jg))))))

(defn spread-black
  [jg]
  (if (check-axioms jg)
    ;; nothing to do, everything checks out
    (do (when @debugging? (println "All axioms satisfied in spread-black."))
        jg)
    ;; something to do (inconsistent), spread black.
    ;; - bad-strokes: a stroke is white but has all black incoming nodes;
    ;;   or, it points to a black node with no white strokes; turn it black.
    ;; - bad-nodes: a node is white but has all black incoming strokes;
    ;;   or, one of its outgoing strokes is black; turn it black.
    (let [bad-strokes (filter (fn [s] (and (white? jg s)
                                           (not (bottom? s))
                                           (or (and (not-empty (jgin jg s))
                                                    (every? (fn [n] (black? jg n))
                                                            (jgin jg s)))
                                               (and (black? jg (first (jgout jg s)))
                                                    (every? (fn [s2] (white? jg s2))
                                                            (jgin jg (first (jgout jg s))))))))
                              (strokes jg))
          bad-nodes (filter (fn [n] (and (white? jg n)
                                         (not (bottom? n))
                                         (or (some (fn [s] (black? jg s)) (jgin jg n))
                                             (some (fn [s] (black? jg s)) (jgout jg n)))))
                            (nodes jg))]
      (when @debugging?
        (println "found bad strokes:" bad-strokes)
        (println "found bad nodes:" bad-nodes))
      (cond
        (not-empty bad-strokes)
          (let [best-bad-stroke (first bad-strokes)]
            (when @debugging?
              (println "choosing bad stroke:" best-bad-stroke))
            (recur (assert-black jg best-bad-stroke)))
        (not-empty bad-nodes)
          (let [best-bad-node (first bad-nodes)]
            (when @debugging?
              (println "choosing bad node:" best-bad-node))
            (recur (assert-black jg best-bad-node)))
        :otherwise
        (do (when @debugging? (println "Axioms failed in spread-black."))
            jg)))))

;; TODO: should expand always introduce a new stroke?
(defn expand
  [jg node]
  (let [jg2 (-> jg (assert-black node)
                (spread-black))]
    ;; if it didn't work out (no way to spread-black consistently), spread-white to make up for it
    (if (check-axioms jg2)
      jg2
      (spread-white jg2))))

(defn contract
  [jg node]
  (let [jg2 (-> jg (assert-white node)
                (spread-white))]
    ;; if it didn't work out (no way to spread-white consistently), spread-black to make up for it
    (if (check-axioms jg2)
      jg2
      (spread-black jg2))))
