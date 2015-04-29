(ns paragon.core
  (:require [clojure.set :as set])
  (:require [clojure.string :as str])
  (:require [loom.graph :as graph])
  (:require [loom.alg :as graphalg])
  (:require [loom.attr :as graphattr])
  (:require [loom.io :as graphio])
  (:require [clojure.java.shell :as shell])
  (:require [taoensso.timbre.profiling :refer [defnp]])
  (:require [clojure.math.combinatorics :as combo]))

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
  (filter (fn [n] (black? jg n)) (nodes jg)))

(defn disbelieved
  "Returns white nodes."
  [jg]
  (filter (fn [n] (white? jg n)) (nodes jg)))

(defn jgout
  [jg stroke-or-node]
  (graph/neighbors (:graph jg) stroke-or-node))

(defn jgin
  [jg stroke-or-node]
  (graph/incoming (:graph jg) stroke-or-node))

(defn premise?
  [jg node]
  (assert (node? jg node))
  ;; this node has some stroke that has no incoming nodes
  (some (fn [s] (empty? (jgin jg s))) (jgin jg node)))

(defnp visualize-dot
  [jg node-labels? stroke-labels?]
  (let [g (:graph jg)
        g-nodes (-> g
                    (graphattr/add-attr-to-nodes :fillcolor :white (filter #(white? jg %) (nodes jg)))
                    (graphattr/add-attr-to-nodes :fillcolor :black (filter #(black? jg %) (nodes jg)))
                    (graphattr/add-attr-to-nodes :fontcolor :white (filter #(black? jg %) (nodes jg)))
                    (graphattr/add-attr-to-nodes :fontcolor :black (filter #(white? jg %) (nodes jg))))
        g-strokes (-> g-nodes
                      (graphattr/add-attr-to-nodes :shape :plain (strokes jg))
                      (graphattr/add-attr-to-nodes :height 0.1 (strokes jg))
                      (graphattr/add-attr-to-nodes :fillcolor :white (filter #(white? jg %) (strokes jg)))
                      (graphattr/add-attr-to-nodes :fillcolor :black (filter #(black? jg %) (strokes jg)))
                      (graphattr/add-attr-to-nodes :fontcolor :white (filter #(black? jg %) (strokes jg)))
                      (graphattr/add-attr-to-nodes :fontcolor :black (filter #(white? jg %) (strokes jg))))
        g-stroke-labels (reduce (fn [g s] (graphattr/add-attr g s :label (if stroke-labels? (jgstr s) "&nbsp;")))
                                g-strokes (strokes jg))
        g-node-labels (reduce (fn [g n] (graphattr/add-attr g n :label (if node-labels? (jgstr n) "&nbsp;")))
                              g-stroke-labels (nodes jg))]
    ;; add bottom node properties (if bottom node exists)
    (-> g-node-labels
        (graphattr/add-attr :bottom :label "&perp;")
        (graphattr/add-attr :bottom :fontsize "32")
        (graphattr/add-attr :bottom :shape :none))))

(defn visualize
  [jg & {:keys [node-labels? stroke-labels?] :or {node-labels? true stroke-labels? false}}]
  (graphio/view (visualize-dot jg node-labels? stroke-labels?)
                :node {:fillcolor :white :style :filled :fontname "sans"}))

(defn save-pdf
  [jg fname & {:keys [node-labels? stroke-labels?] :or {node-labels? false stroke-labels? false}}]
  (let [dot (graphio/dot-str (visualize-dot jg node-labels? stroke-labels?)
                             :node {:fillcolor :white :style :filled :fontname "sans"})
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
  [jg & nodes]
  (reduce (fn [jg2 n]
            (let [stroke (format ".%s" (jgstr n))]
              (exists-just jg2 [stroke] n)))
          jg nodes))

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

(defn- can-explain-single-hyp
  "Link hyp to explananda via an intermediate stroke."
  [jg hyp explananda]
  (reduce (fn [jg2 ev]
            (let [stroke (format "%sEXP%s" (jgstr hyp) (jgstr ev))]
              (-> jg2
                  (forall-just [hyp] stroke)
                  (exists-just [stroke] ev))))
          jg explananda))

(defn- can-explain-conjunction-hyp
  "Link each in explanatia to strokes that point to a special conjunction node (one for each explananda),
   which then links to each explananda."
  [jg explanantia explananda]
  (reduce (fn [jg2 ev]
            (let [stroke (format "%sEXP%s" (str/join "AND" (map jgstr explanantia)) (jgstr ev))
                  jg-hyps-stroke (forall-just jg2 explanantia stroke)]
              (exists-just jg-hyps-stroke [stroke] ev)))
          jg explananda))

(defnp can-explain
  "The explananda, as a conjunction, justify each of the explanantia."
  [jg explanantia explananda]
  (assert (and (sequential? explanantia) (sequential? explananda)))
  (if (second explanantia)
    (can-explain-conjunction-hyp jg explanantia explananda)
    (can-explain-single-hyp jg (first explanantia) explananda)))

(defnp add-inconsistencies
  "Indicate nodes that cannot all be simultaneously believed.

  Usage example: (add-inconsistencies jg [:node1 :node2 :node3] [:node2 :node3] ...)"
  [jg & nodesets]
  (reduce (fn [jg2 nodes]
            (let [botstroke (format "bot_%s" (str/join "-" (map jgstr nodes)))]
              (-> jg2
                  (forall-just nodes botstroke)
                  (exists-just [botstroke] :bottom))))
          jg nodesets))

(defn spread-white-default-strategy
  "Guaranteed that bad-nodes is not empty."
  [_ bad-nodes]
  (let [best-bad-node (last (sort-by jgstr bad-nodes))]
    (when @debugging?
      (println "Choosing bad node:" best-bad-node))
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

(defnp spread-white
  [jg white-strategy]
  (loop [jg jg]
    (if (check-color-axioms jg)
      ;; nothing to do, everything checks out
      (do (when @debugging? (println "All axioms satisfied in spread-white."))
          jg)
      ;; something to do (inconsistent), spread white
      (let [bad-strokes (delay (spread-white-bad-strokes jg))
            bad-nodes-deterministic (delay (spread-white-bad-nodes-deterministic jg))
            bad-nodes-nondeterministic (delay (spread-white-bad-nodes-nondeterministic jg))]
        (when @debugging?
          (println "Spreading white.")
          (println "Found bad strokes:" @bad-strokes)
          (println "Found bad nodes (deterministic):" @bad-nodes-deterministic)
          (println "Found bad nodes (non-deterministic):" @bad-nodes-nondeterministic))
        (cond
          ;; if we have bad strokes, just take care of them; no need for strategy
          ;; or, if we have deterministic bad nodes, just take care of them; no need for strategy
          (or (not-empty @bad-strokes) (not-empty @bad-nodes-deterministic))
          (recur (reduce assert-white jg (concat @bad-strokes @bad-nodes-deterministic)))
          ;; if we have a non-deterministic bad node, employ the strategy
          (not-empty @bad-nodes-nondeterministic)
          (recur (assert-white jg (white-strategy jg @bad-nodes-nondeterministic)))
          :else
          (do (when @debugging? (println "Axioms failed in spread-white."))
              jg))))))

(defn spread-abduce-default-strategy
  "Guaranteed that bad-strokes is not empty."
  [_ bad-strokes]
  (let [best-bad-stroke (first (sort-by jgstr bad-strokes))]
    (when @debugging?
      (println "Choosing bad stroke:" best-bad-stroke))
    best-bad-stroke))

(defnp spread-abduce-bad-strokes-deterministic
  "Bad stroke w.r.t. abduction (deterministic): A stroke is white but all its incoming nodes are black."
  [jg]
  (filter (fn [s] (and (white? jg s)
                       (and (not-empty (jgin jg s))
                            (every? (fn [n] (black? jg n))
                                    (jgin jg s)))))
          (strokes jg)))

(defnp spread-abduce-bad-strokes-nondeterministic
  "Bad stroke w.r.t. abduction (non-deterministic): A stroke is white but points to a black node that
  has only white strokes pointing to it."
  [jg]
  (filter (fn [s] (and (white? jg s)
                       (black? jg (first (jgout jg s)))
                       (every? (fn [s2] (white? jg s2))
                               (jgin jg (first (jgout jg s))))))
          (strokes jg)))

(defnp spread-abduce-bad-nodes
  "Bad node w.r.t. abduction: A node is white but is pointed to by a black stroke or points to a black stroke."
  [jg]
  (filter (fn [n] (and (white? jg n)
                       (or (some (fn [s] (black? jg s)) (jgin jg n))
                           (some (fn [s] (black? jg s)) (jgout jg n)))))
          (nodes jg)))

(defnp spread-abduce
  [jg abduce-strategy]
  (loop [jg jg]
    (if (check-color-axioms jg)
      ;; nothing to do, everything checks out
      (do (when @debugging? (println "All axioms satisfied in spread-abduce."))
          jg)
      ;; something to do (inconsistent), spread abductively
      (let [bad-strokes-deterministic (delay (spread-abduce-bad-strokes-deterministic jg))
            bad-strokes-nondeterministic (delay (spread-abduce-bad-strokes-nondeterministic jg))
            bad-nodes (delay (spread-abduce-bad-nodes jg))]
        (when @debugging?
          (println "Spreading abductively.")
          (println "Found bad strokes (deterministic):" @bad-strokes-deterministic)
          (println "Found bad strokes (non-deterministic):" @bad-strokes-nondeterministic)
          (println "Found bad nodes:" @bad-nodes))
        (cond
          ;; if we have deterministic bad strokes and/or nodes, just take care of them; no need for strategy
          (or (not-empty @bad-strokes-deterministic) (not-empty @bad-nodes))
          (recur (reduce assert-black jg (concat @bad-strokes-deterministic @bad-nodes)))
          ;; if we have a non-deterministic bad stroke, employ the strategy
          (not-empty @bad-strokes-nondeterministic)
          (recur (assert-black jg (abduce-strategy jg @bad-strokes-nondeterministic)))
          :else
          (do (when @debugging? (println "Axioms failed in spread-abduce."))
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

(defnp spread-black
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
          (let [to-assert-black (concat bad-strokes bad-nodes)]
            (recur (reduce assert-black jg to-assert-black)))
          (do (when @debugging? (println "Axioms failed in spread-black."))
              jg))))))

(defnp contract
  "Only colors white (upwards and downwards). A \"strategy\" is needed. Uses white-strategy for now."
  [jg nodes & {:keys [white-strategy abd?]
               :or {white-strategy spread-white-default-strategy
                    abd? false}}]
  (assert (sequential? nodes))
  (when @debugging? (println "Contracting by" nodes))
  (let [jg-asserted (reduce (fn [jg2 node]
                              (assert-white jg2 (if abd? (format ".%s" (jgstr node)) node)))
                            jg nodes)
        jg-whitened (spread-white jg-asserted white-strategy)]
    ;; if it didn't work out (no way to spread-white consistently), return nil
    (if (check-color-axioms jg-whitened)
      jg-whitened
      nil)))

(defnp abduce
  "Only colors black (upwards and downwards). A \"strategy\" is needed."
  [jg nodes & {:keys [abduce-strategy white-strategy]
               :or {abduce-strategy spread-abduce-default-strategy
                    white-strategy spread-white-default-strategy}}]
  (assert (sequential? nodes))
  (let [jg-asserted (reduce assert-black jg nodes)
        jg-blackened (spread-abduce jg-asserted abduce-strategy)]
    ;; if it didn't work out (no way to spread-black consistently), return nil
    (cond
      (check-color-axioms jg-blackened)
      jg-blackened
      (black? jg-blackened :bottom)
      (contract jg-blackened [:bottom] :white-strategy white-strategy)
      :else
      nil)))

(defnp expand
  "Only colors black, and only downwards, except when 'bottom' is colored black.
   A white-strategy is needed in case 'bottom' is turned black and contraction is required."
  [jg nodes & {:keys [white-strategy]
               :or {white-strategy spread-white-default-strategy}}]
  (assert (sequential? nodes))
  (let [jg-asserted (reduce assert-black jg nodes)
        jg-blackened (spread-black jg-asserted)]
    (cond
      (check-color-axioms jg-blackened)
      jg-blackened
      (black? jg-blackened :bottom)
      (contract jg-blackened [:bottom] :white-strategy white-strategy)
      :else
      nil)))

(defn convert-to-com-input
  [jg contract-ns]
  (format "%s\n\n[%s] ?- [%s]."
          (str/join "\n" (for [n (nodes jg)]
                           (format "node(%s)." (jgstr n))))
          (str/join ", " (for [n (nodes jg)
                               s (jgin jg n)]
                           (if (empty? (jgin jg s))
                             (format "[[%s], %s]" (jgstr n) (jgstr n))
                             (format "[[%s], %s]" (str/join ", " (map jgstr (jgin jg s))) (jgstr n)))))
          (str/join "," (map jgstr contract-ns))))

(defn parse-com-output
  [jg output]
  (spread-black
   (reduce (fn [jg [premises conclusion]]
             (if (= premises conclusion)
               (-> jg (assert-black (format "s%s" conclusion))
                   (assert-black conclusion))
               (reduce assert-black jg (conj (str/split premises #"\s*,\s*") conclusion))))
           (reduce assert-white jg (concat (nodes jg) (strokes jg)))
           (map #(str/split % #"\s*\|-\s*")
                (re-seq #"[\w,]+ \|- \w+" (second (re-find #"(?s)ANSWER: (.*?)####" output)))))))

(defn process-with-com
  [jg contract-ns mm?]
  (let [input-str (convert-to-com-input jg contract-ns)]
    (when @debugging? (println input-str))
    (spit "test-com.pl" input-str)
    (let [{output :out} (shell/sh "changes-of-mind/a.out" "test-com.pl" (if mm? "on" "off"))]
      (when @debugging? (println output))
      (try (parse-com-output jg output)
           (catch Exception _ (println input-str) (println output) (throw (Exception.)))))))

(defn convert-to-prolog
  [jg]
  (let [rules (for [n (nodes jg)
                    :when (and (not= n :bottom) (not (premise? jg n)))
                    s (jgin jg n)]
                {:head n :body (jgin jg s)})
        inconsistencies (reduce (fn [m s]
                                  (let [incon (jgin jg s)]
                                    (reduce (fn [m2 n]
                                              (update-in m2 [n] conj (filter #(not= n %) incon)))
                                            m incon)))
                                {} (jgin jg :bottom))
        preds (concat (map #(format "premise(%s)." (jgstr %))
                           (filter #(premise? jg %) (nodes jg)))
                      (map #(format "b(%s)." (jgstr %))
                           (filter #(premise? jg %) (believed jg)))
                      (map (fn [rule]
                             (let [rule-body (map #(format "believed(%s)" (jgstr %))
                                                  (:body rule))]
                               (format "believed(%s) :- %s."
                                       (jgstr (:head rule)) (str/join ", " rule-body))))
                           rules)
                      (mapcat (fn [[n incon-groups]]
                                (map (fn [incon-group]
                                       (format "consistent(%s) :- %s."
                                               (jgstr n)
                                               (str/join ", " (map (fn [incon] (format "disbelieved(%s)" (jgstr incon)))
                                                                   incon-group))))
                                     (apply combo/cartesian-product incon-groups)))
                              (seq inconsistencies))
                      ;; all nodes not mentioned in inconsistencies map get default consistency
                      (map (fn [n] (format "consistent(%s)." (jgstr n)))
                           (filter (fn [n] (and (not= :bottom n) (nil? (inconsistencies n)))) (nodes jg)))
                      ["assertwhite(X) :- retract(b(X))."
                       "assertblack(X) :- premise(X), assert(b(X)), allconsistent.\nassertblack(X) :- premise(X), retract(b(X))."
                       "believed(X) :- premise(X), b(X)."
                       "disbelieved(X) :- \\+b(X)."
                       "allconsistent :- forall(believed(X), consistent(X))."])]
    (str
      ":- dynamic b/1.\n"
      (str/join "\n" (sort preds)))))
