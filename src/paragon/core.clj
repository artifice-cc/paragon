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

(defn abducible?
  [node]
  (= \? (first (seq (jgstr node)))))

(defn conjunction?
  [node]
  (re-find #"\+" (jgstr node)))

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
  (filter (fn [n] (and (not (abducible? n)) (not (conjunction? n)) (black? jg n))) (nodes jg)))

(defn disbelieved
  "Returns white nodes."
  [jg]
  (filter (fn [n] (and (not (abducible? n)) (not (conjunction? n)) (white? jg n))) (nodes jg)))

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
  (if @debugging?
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

(defn- assert-color
  [jg stroke-or-node color]
  (when @debugging? (println "asserting" stroke-or-node "as" color))
  (assoc-in jg [:coloring stroke-or-node] color))

(defn- assert-black
  [jg stroke-or-node]
  (assert-color jg stroke-or-node :black))

(defn- assert-white
  [jg stroke-or-node]
  (assert-color jg stroke-or-node :white))

(defn hypothesis
  [jg hyp]
  (-> jg
      (exists-just [(format ".?%s" (jgstr hyp))] (format "?%s" (jgstr hyp)))
      (forall-just [(format "?%s" (jgstr hyp))] (format ".%s" (jgstr hyp)))
      (exists-just [(format ".%s" (jgstr hyp))] hyp)
      (assert-black (format ".?%s" (jgstr hyp)))
      (assert-black (format "?%s" (jgstr hyp)))))

(defn- can-explain-single-hyp
  "Link explananda to hyp via an intermediate stroke, and connect hyp's hypothesis ?* node."
  [jg hyp explananda]
  (reduce (fn [jg2 ev]
            (-> jg2
                (premise ev)
                (forall-just [ev] (format ".%s" (jgstr hyp)))))
          jg explananda))

(defn- can-explain-conjunction-hyp
  "Link explananda to a special conjunction node for the explanantia, which links to each node in the conjunction."
  [jg explanantia explananda]
  (let [s (format "%s_%s"
                  (str/join "+" (map jgstr explananda))
                  (str/join "+" (map jgstr explanantia)))
        n (str/join "+" (map jgstr explanantia))
        jg-abducibles (reduce (fn [jg2 hyp]
                                (forall-just jg2 [(format "?%s" (jgstr hyp)) n] (format ".%s" (jgstr hyp))))
                              jg explanantia)
        jg-evidence (reduce (fn [jg2 ev] (forall-just jg2 [ev] s))
                            jg-abducibles explananda)]
    (exists-just jg-evidence [s] n)))

(defn can-explain
  "The explananda, as a conjunction, justify each of the explanantia."
  [jg explanantia explananda]
  (assert (and (sequential? explanantia) (sequential? explananda)))
  (let [jg-hyps (reduce (fn [jg hyp] (hypothesis jg hyp)) jg explanantia)]
    (if (second explanantia)
      (can-explain-conjunction-hyp jg-hyps explanantia explananda)
      (can-explain-single-hyp jg-hyps (first explanantia) explananda))))

(defn add-inconsistencies
  "Indicate nodes that cannot all be simultaneously believed.

  Usage example: (add-inconsistencies jg [:node1 :node2 :node3])"
  [jg nodes]
  (let [botstroke (format "bot_%s" (str/join "-" (map jgstr nodes)))]
    (-> jg
        (forall-just nodes botstroke)
        (exists-just [botstroke] :bottom))))

(defn spread-white-default-strategy
  "Guaranteed that bad-strokes or bad-nodes is not empty."
  [_ bad-strokes bad-nodes]
  (if (not-empty bad-strokes)
    (let [best-bad-stroke (first bad-strokes)]
      (when @debugging?
        (println "Choosing bad stroke:" best-bad-stroke))
      best-bad-stroke)
    (let [best-bad-node (if (some abducible? bad-nodes)
                          (first (filter abducible? bad-nodes))
                          (first bad-nodes))]
      (when @debugging?
        (println "Choosing bad node:" best-bad-node))
      best-bad-node)))

(defn spread-black-default-strategy
  "Guaranteed that bad-strokes or bad-nodes is not empty."
  [_ bad-strokes bad-nodes]
  (if (not-empty bad-strokes)
    (let [best-bad-stroke (first bad-strokes)]
      (when @debugging?
        (println "Choosing bad stroke:" best-bad-stroke))
      best-bad-stroke)
    (let [best-bad-node (first bad-nodes)]
      (when @debugging?
        (println "Choosing bad node:" best-bad-node))
      best-bad-node)))

(defn- spread-white
  [jg strategy]
  (if (check-axioms jg)
    ;; nothing to do, everything checks out
    (do (when @debugging? (println "All axioms satisfied in spread-white."))
        jg)
    ;; something to do (inconsistent), spread white
    (let [bad-strokes (filter (fn [s] (and (black? jg s)
                                           (or (some (fn [n] (white? jg n)) (jgin jg s))
                                               (white? jg (first (jgout jg s))))))
                              (strokes jg))
          bad-nodes (filter (fn [n] (and (black? jg n)
                                         (or (every? (fn [s] (white? jg s)) (jgin jg n))
                                             (some (fn [s] (and (white? jg s)
                                                                (every? (fn [n2] (black? jg n2)) (jgin jg s))))
                                                   (jgout jg n)))))
                            (nodes jg))]
      (when @debugging?
        (println "Spreading white.")
        (println "Found bad strokes:" bad-strokes)
        (println "Found bad nodes:" bad-nodes))
      (if (or (not-empty bad-strokes) (not-empty bad-nodes))
        (recur (assert-white jg (strategy jg bad-strokes bad-nodes)) strategy)
        (do (when @debugging? (println "Axioms failed in spread-white."))
            jg)))))

(defn- spread-black
  [jg strategy]
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
        (println "Spreading black.")
        (println "Found bad strokes:" bad-strokes)
        (println "Found bad nodes:" bad-nodes))
      (if (or (not-empty bad-strokes) (not-empty bad-nodes))
        (recur (assert-black jg (strategy jg bad-strokes bad-nodes)) strategy)
        (do (when @debugging? (println "Axioms failed in spread-black."))
            jg)))))

(defn expand
  [jg nodes & {:keys [white-strategy black-strategy]
               :or {white-strategy spread-white-default-strategy
                    black-strategy spread-black-default-strategy}}]
  (assert (sequential? nodes))
  (let [jg-asserted (reduce (fn [jg2 node]
                              (assert-black jg2 (format ".%s" (jgstr node))))
                            jg nodes)
        jg-blackened (spread-black jg-asserted black-strategy)]
    ;; if it didn't work out (no way to spread-black consistently), spread-white to make up for it
    (if (check-axioms jg-blackened)
      jg-blackened
      (spread-white jg-blackened white-strategy))))

(defn contract
  [jg nodes & {:keys [white-strategy black-strategy]
               :or {white-strategy spread-white-default-strategy
                    black-strategy spread-black-default-strategy}}]
  (assert (sequential? nodes))
  (let [jg-asserted (reduce (fn [jg2 node]
                              (assert-white jg2 (format ".%s" (jgstr node))))
                            jg nodes)
        jg-whitened (spread-white jg-asserted white-strategy)]
    ;; if it didn't work out (no way to spread-white consistently), spread-black to make up for it
    (if (check-axioms jg-whitened)
      jg-whitened
      (spread-black jg-whitened black-strategy))))
