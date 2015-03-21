(ns paragon.core
  (:require [clojure.set :as set])
  (:require [clojure.string :as str])
  (:require [loom.graph :as graph])
  (:require [loom.alg :as graphalg])
  (:require [loom.attr :as graphattr])
  (:require [loom.io :as graphio])
  (:require [clojure.java.shell :as shell])
  (:require [taoensso.timbre.profiling :refer [defnp]]))

(def debugging? (atom false))

(defn turn-on-debugging [] (swap! debugging? (constantly true)))
(defn turn-off-debugging [] (swap! debugging? (constantly false)))

(defn jgstr
  [stroke-or-node]
  (cond (keyword? stroke-or-node)
        (name stroke-or-node)
        (map? stroke-or-node)
        (str (:id stroke-or-node))
        :else
        (str stroke-or-node)))

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

(defn remove-node-or-stroke
  [jg node-or-stroke]
  (-> jg
      (update-in [:graph] graph/remove-nodes node-or-stroke)
      (update-in [:types] dissoc node-or-stroke)
      (update-in [:coloring] dissoc node-or-stroke)))

(defn jgcolor
  [jg stroke-or-node]
  (get-in jg [:coloring stroke-or-node] :white))

(defn jgtype
  [jg stroke-or-node]
  (get-in jg [:types stroke-or-node]))

(defn degree
  [jg stroke-or-node]
  (+ (graph/in-degree (:graph jg) stroke-or-node)
     (graph/degree (:graph jg) stroke-or-node)))

(defn in-degree
  [jg stroke-or-node]
  (graph/in-degree (:graph jg) stroke-or-node))

(defn out-degree
  [jg stroke-or-node]
  (graph/degree (:graph jg) stroke-or-node))

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

(defn hypothesis?
  [jg node]
  (graph/has-node? (:graph jg) (format "?%s" (jgstr node))))

(defnp explainers
  [jg node]
  (let [ss (jgout jg node)
        ns (set (mapcat #(jgout jg %) ss))
        hyps (set (filter #(= \? (first (seq (jgstr %))))
                          (set (mapcat #(jgin jg %) ss))))]
    ;; some outgoing node from some stroke that 'node' points to is a hyp node
    (filter (fn [n] (hyps (format "?%s" (jgstr n)))) ns)))

(defnp explains
  [jg node]
  (filter (fn [n] (and (not= \? (first (seq (jgstr n))))
                       (not (re-find #"\+" (jgstr n)))))
          (set (mapcat #(jgin jg %) (jgin jg node)))))

(defnp visualize-dot
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
                              g-strokes (nodes jg))]
    ;; add bottom node properties (if bottom node exists)
    (-> g-node-labels
        (graphattr/add-attr :bottom :label "&perp;")
        (graphattr/add-attr :bottom :fontsize "32")
        (graphattr/add-attr :bottom :shape :none))))

(defn visualize
  [jg]
  (graphio/view (visualize-dot jg) :node {:fillcolor :white :style :filled :fontname "sans"}))

(defn save-pdf
  [jg fname]
  (let [dot (graphio/dot-str (visualize-dot jg) :node {:fillcolor :white :style :filled :fontname "sans"})
        {pdf :out} (shell/sh "dot" "-Tpdf" :in dot :out-enc :bytes)]
    (with-open [w (java.io.FileOutputStream. fname)]
      (.write w pdf))))

(defnp check-axiom-neg1
  "Everything is black or white."
  [jg]
  (every? #{:white :black} (vals (:coloring jg))))

(defn check-axiom-0
  "Nothing is both black and white.

  Axiom 0 is confirmed from the fact that :coloring is a map."
  [jg]
  true)

(defnp check-axiom-1
  [jg]
  "Everything is either a node or a stroke."
  (every? #{:node :stroke} (vals (:types jg))))

(defn check-axiom-2
  "Nothing is both a node and a stroke.

  Axiom 2 is confirmed from the fact that :types is a map."
  [jg]
  true)

(defnp check-axiom-3-and-4
  "Strokes send arrows only to nodes. Nodes send arrows only to strokes."
  [jg]
  (every? (fn [[start end]]
            (cond (stroke? jg start) (node? jg end)
                  (node? jg start) (stroke? jg end)
                  :else nil))
          (graph/edges (:graph jg))))

(defnp check-axiom-5
  "Every stroke sends an arrow to exactly one thing."
  [jg]
  (every? (fn [stroke] (= 1 (count (jgout jg stroke))))
          (strokes jg)))

(defnp check-axiom-6
  "Arrowing is one-way."
  [jg]
  (every? (fn [[n-or-s1 n-or-s2]]
            (not (graph/has-edge? (:graph jg) n-or-s2 n-or-s1)))
          (graph/edges (:graph jg))))

(defnp check-axiom-7
  "If two strokes send arrows to the same thing, and the things from which one of them receives arrows are among those from which the other receives arrows, then those strokes are identical."
  [jg]
  (let [ss (strokes jg)]
    (every? (fn [s] (every? (fn [s2] (= s s2))
                            ;; find strokes s2 where s2's incoming arrows are subseteq of incoming arrows of s
                            (filter (fn [s2]
                                      (and (not-empty (jgin jg s))
                                           (not-empty (jgin jg s2))
                                           (every? (set (jgin jg s)) (jgin jg s2))))
                                    ;; find strokes that have an arrow to the same node
                                    (filter (fn [s2] (= (first (jgout jg s))
                                                        (first (jgout jg s2))))
                                            ss))))
            ss)))

(defnp check-axiom-8
  "Every node receives an arrow."
  [jg]
  (every? (fn [node] (not-empty (jgin jg node)))
          (nodes jg)))

(defnp check-axiom-coloration-1
  "Every black node receives an arrow from some black inference stroke."
  [jg]
  (every? (fn [node] (or (white? jg node)
                         (some (fn [in] (and (stroke? jg in) (black? jg in)))
                               (jgin jg node))))
          (nodes jg)))

(defnp check-axiom-coloration-2
  "Every white node receives arrows only from white inference strokes."
  [jg]
  (every? (fn [node] (or (black? jg node)
                         (every? (fn [in] (and (stroke? jg in)
                                               (white? jg in)))
                                 (jgin jg node))))
          (nodes jg)))

(defnp check-axiom-coloration-3
  "Every black inference stroke receives arrows (if any) only from black nodes."
  [jg]
  (every? (fn [stroke] (or (white? jg stroke)
                           (empty? (jgin jg stroke))
                           (every? (fn [n] (and (node? jg n) (black? jg n)))
                                   (jgin jg stroke))))
          (strokes jg)))

(defnp check-axiom-coloration-4
  "Every white inference stroke that receives an arrow receives an arrow from some white node."
  [jg]
  (every? (fn [stroke] (or (black? jg stroke)
                           (empty? (jgin jg stroke))
                           (some (fn [in] (and (node? jg in)
                                               (white? jg in)))
                                 (jgin jg stroke))))
          (strokes jg)))

(defnp check-axiom-coloration-bottom
  "The node 'bottom' is white."
  [jg]
  (or (not (node? jg :bottom)) (white? jg :bottom)))

(defn check-structure-axioms-debug
  [jg]
  (and (or (check-axiom-neg1 jg) (println "Fails Axiom -1."))
       (or (check-axiom-0 jg) (println "Fails Axiom 0."))
       (or (check-axiom-1 jg) (println "Fails Axiom 1."))
       (or (check-axiom-2 jg) (println "Fails Axiom 2."))
       (or (check-axiom-3-and-4 jg) (println "Fails Axioms 3/4."))
       (or (check-axiom-5 jg) (println "Fails Axiom 5."))
       (or (check-axiom-6 jg) (println "Fails Axiom 6."))
       (or (check-axiom-7 jg) (println "Fails Axiom 7."))
       (or (check-axiom-8 jg) (println "Fails Axiom 8."))))

(defn check-color-axioms-debug
  [jg]
  (and (or (check-axiom-coloration-1 jg) (println "Fails Axiom of Coloration 1."))
       (or (check-axiom-coloration-2 jg) (println "Fails Axiom of Coloration 2."))
       (or (check-axiom-coloration-3 jg) (println "Fails Axiom of Coloration 3."))
       (or (check-axiom-coloration-4 jg) (println "Fails Axiom of Coloration 4."))
       (or (check-axiom-coloration-bottom jg) (println "Fails Axiom of Coloration Bottom."))))

(defn check-structure-axioms
  [jg]
  (if @debugging?
    (check-structure-axioms-debug jg)
    (and (check-axiom-neg1 jg)
         (check-axiom-0 jg)
         (check-axiom-1 jg)
         (check-axiom-2 jg)
         (check-axiom-3-and-4 jg)
         (check-axiom-5 jg)
         (check-axiom-6 jg)
         (check-axiom-7 jg)
         (check-axiom-8 jg))))

(defn check-color-axioms
  [jg]
  (if @debugging?
    (check-color-axioms-debug jg)
    (and (check-axiom-coloration-1 jg)
         (check-axiom-coloration-2 jg)
         (check-axiom-coloration-3 jg)
         (check-axiom-coloration-4 jg)
         (check-axiom-coloration-bottom jg))))

(defnp forall-just
  [jg nodes stroke]
  (reduce (fn [jg2 node] (-> jg2
                             (assoc-in [:types node] :node)
                             (update-in [:graph] graph/add-edges [node stroke])))
          (assoc-in jg [:types stroke] :stroke) nodes))

(defnp exists-just
  [jg strokes node]
  (reduce (fn [jg2 stroke] (-> jg2
                               (assoc-in [:types stroke] :stroke)
                               (update-in [:graph] graph/add-edges [stroke node])))
          (assoc-in jg [:types node] :node) strokes))

(defn premise
  [jg node]
  (let [stroke (format ".%s" (jgstr node))]
    (exists-just jg [stroke] node)))

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
                ;; make the ?hyp node point to this new stroke, if there is a ?hyp node
                (forall-just (if (hypothesis? jg ev)
                               [ev (format "?%s" (jgstr ev))] [ev])
                             (format ".%s" (jgstr hyp)))))
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
        jg-evidence (reduce (fn [jg2 ev] (forall-just jg2 (if (hypothesis? jg ev)
                                                            [ev (format "?%s" (jgstr ev))] [ev])
                                                      s))
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
        (forall-just (mapcat (fn [n] (if (graph/has-node? (:graph jg) (format "?%s" (jgstr n)))
                                       [n (format "?%s" (jgstr n))] [n])) nodes)
                     botstroke)
        (exists-just [botstroke] :bottom))))

(defn spread-white-default-strategy
  "Guaranteed that bad-strokes or bad-nodes is not empty."
  [_ bad-nodes]
  (let [best-bad-node (if (some abducible? bad-nodes)
                        (first (filter abducible? bad-nodes))
                        (first bad-nodes))]
    (when @debugging?
      (println "Choosing bad node:" best-bad-node
               "abducible?" (= best-bad-node (first (filter abducible? bad-nodes)))))
    best-bad-node))

(defnp spread-white-bad-strokes
  "Bad stroke w.r.t. white: A stroke is black but points a white node, or
  a stroke is black but some white node points to it."
  [jg]
  (filter (fn [s] (and (black? jg s)
                       (or (white? jg (first (jgout jg s)))
                           (some (fn [n] (white? jg n)) (jgin jg s)))))
          (strokes jg)))

(defnp spread-white-bad-nodes-deterministic
  "Bad node w.r.t. white (deterministic): A node is black but all of its incoming strokes are white."
  [jg]
  (filter (fn [n] (and (black? jg n)
                       (every? (fn [s] (white? jg s)) (jgin jg n))))
          (nodes jg)))

(defnp spread-white-bad-nodes-nondeterministic
  "Bad node w.r.t. white (non-deterministic): A node is black but points to a white stroke that
  has only black nodes pointing to it."
  [jg]
  (filter (fn [n] (and (black? jg n)
                       (some (fn [s] (and (white? jg s)
                                          (every? (fn [n2] (black? jg n2)) (jgin jg s))))
                             (jgout jg n))))
          (nodes jg)))

(defn spread-white
  [jg white-strategy]
  (loop [jg jg]
    (if (check-color-axioms jg)
      ;; nothing to do, everything checks out
      (do (when @debugging? (println "All axioms satisfied in spread-white."))
          jg)
      ;; something to do (inconsistent), spread white
      (let [bad-strokes (spread-white-bad-strokes jg)
            bad-nodes-deterministic (spread-white-bad-nodes-deterministic jg)
            bad-nodes-nondeterministic (spread-white-bad-nodes-nondeterministic jg)]
        (when @debugging?
          (println "Spreading white.")
          (println "Found bad strokes:" bad-strokes)
          (println "Found bad nodes (deterministic):" bad-nodes-deterministic)
          (println "Found bad nodes (non-deterministic):" bad-nodes-nondeterministic))
        (cond
          ;; if we have a bad stroke, just take care of it; no need for strategy
          (not-empty bad-strokes)
          (recur (assert-white jg (first bad-strokes)))
          ;; if we have a deterministic bad node, just take care of it; no need for strategy
          (not-empty bad-nodes-deterministic)
          (recur (assert-white jg (first bad-nodes-deterministic)))
          ;; if we have a non-deterministic bad node, employ the strategy
          (not-empty bad-nodes-nondeterministic)
          (recur (assert-white jg (white-strategy jg bad-nodes-nondeterministic)))
          :else
          (do (when @debugging? (println "Axioms failed in spread-white."))
              jg))))))

(defnp spread-black-bad-strokes
  "Bad stroke w.r.t. black: A stroke is white but has all incoming black nodes."
  [jg]
  (filter (fn [s] (and (white? jg s)
                       (and (not-empty (jgin jg s))
                            (every? (fn [n] (black? jg n))
                                    (jgin jg s)))))
          (strokes jg)))

(defnp spread-black-bad-nodes
  "Bad node w.r.t. black: A node is white but has some incoming black stroke."
  [jg]
  (filter (fn [n] (and (white? jg n)
                       (some (fn [s] (black? jg s)) (jgin jg n))))
          (nodes jg)))

(defn spread-black
  [jg]
  (loop [jg jg]
    (if (check-color-axioms jg)
      ;; nothing to do, everything checks out
      (do (when @debugging? (println "All axioms satisfied in spread-black."))
          jg)
      ;; something to do (inconsistent), spread black.
      (let [bad-strokes (spread-black-bad-strokes jg)
            bad-nodes (spread-black-bad-nodes jg)]
        (when @debugging?
          (println "Spreading black.")
          (println "Found bad strokes:" bad-strokes)
          (println "Found bad nodes:" bad-nodes))
        (if (or (not-empty bad-strokes) (not-empty bad-nodes))
          (let [choice (first (concat bad-strokes bad-nodes))]
            (recur (assert-black jg choice)))
          (do (when @debugging? (println "Axioms failed in spread-black."))
              jg))))))

(defn contract
  "Only colors white (upwards and downwards). A \"strategy\" is needed."
  [jg nodes & {:keys [white-strategy abd?]
               :or {white-strategy spread-white-default-strategy
                    abd? false}}]
  (assert (sequential? nodes))
  (let [jg-asserted (reduce (fn [jg2 node]
                              (assert-white jg2 (if abd? (format ".%s" (jgstr node)) node)))
                            jg nodes)
        jg-whitened (spread-white jg-asserted white-strategy)]
    ;; if it didn't work out (no way to spread-white consistently), return nil
    (if (check-color-axioms jg-whitened)
      jg-whitened
      nil)))

(defn expand
  "Only colors black, and only downwards. A white-strategy is needed in case 'bottom' is turned black."
  [jg nodes & {:keys [white-strategy abd?]
               :or {white-strategy spread-white-default-strategy
                    abd? false}}]
  (assert (sequential? nodes))
  (let [jg-asserted (reduce (fn [jg2 node]
                              (assert-black jg2 (if abd? (format ".%s" (jgstr node)) node)))
                            jg nodes)
        jg-blackened (spread-black jg-asserted)]
    (cond
      (check-color-axioms jg-blackened)
      jg-blackened
      (black? jg-blackened :bottom)
      (contract jg-blackened [:bottom] :white-strategy white-strategy :abd? false)
      :else
      nil)))

