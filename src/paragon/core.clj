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

(defn new-just-graph
  []
  {:types {}
   :coloring {}
   :inconsistent {}
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

(defn jgstr
  [stroke-or-node]
  (if (keyword? stroke-or-node) (name stroke-or-node) (str stroke-or-node)))

(defn uncertainty?
  [stroke-or-node]
  (let [snstr (jgstr stroke-or-node)]
    (or (= "uncertainty-node" snstr)
        (= "uncertainty-stroke" snstr)
        (= "un" (subs snstr 0 (min (count snstr) 2))))))

(defn consistent-if-black?
  [jg stroke-or-node]
  (or (empty? (get-in jg [:inconsistent stroke-or-node]))
      (not-any? (fn [sn-inc] (black? jg sn-inc)) (get-in jg [:inconsistent stroke-or-node]))))

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
  (let [inconsistent-edges (set (for [sn (keys (:inconsistent jg))
                                      sn-inc (get-in jg [:inconsistent sn])]
                                  (sort [sn sn-inc])))
        g-uncertainty (-> (:graph jg)
                          (graph/remove-nodes :uncertainty-stroke :uncertainty-node)
                          ;; make all uncertainty node-specific strokes have label "?"
                          (graphattr/add-attr-to-nodes
                            :label "?" (filter #(= "un" (subs (jgstr %) 0 (min (count (jgstr %)) 2)))
                                               (strokes jg))))
        g-inc-edges (-> (apply graph/add-edges g-uncertainty inconsistent-edges)
                        (graphattr/add-attr-to-edges :style :dotted inconsistent-edges)
                        (graphattr/add-attr-to-edges :arrowhead :none inconsistent-edges)
                        (graphattr/add-attr-to-edges :constraint :false inconsistent-edges))]
    (graphio/view g-inc-edges :node {:fillcolor :white :style :filled :fontname "sans"})))

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
                           (every? (fn [n] (and (node? jg n)
                                                (or (uncertainty? n) (black? jg n))))
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

(defn check-axiom-coloration-uncertainty
  "Extra axiom: Both :uncertainty, :uncertainty-stroke are white."
  [jg]
  (every? (fn [sn] (white? jg sn))
          (filter (fn [sn] (uncertainty? sn)) (concat (nodes jg) (strokes jg)))))

(defn check-axiom-coloration-inconsistencies
  "Extra axiom: No two nodes/strokes of an inconsistent pair are black."
  [jg]
  (every? (fn [sn] (or (empty? (get-in jg [:inconsistent sn]))
                       (white? jg sn)
                       ;; sn is black
                       (not-any? (fn [sn-inc] (black? jg sn-inc)) (get-in jg [:inconsistent sn]))))
          (keys (:inconsistent jg))))

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
       (or (check-axiom-coloration-4 jg) (println "Fails Axiom of Coloration 4."))
       (or (check-axiom-coloration-uncertainty jg) (println "Fails Axiom of Coloration - Uncertainty."))
       (or (check-axiom-coloration-inconsistencies jg) (println "Fails Axiom of Coloration - Inconsistencies."))))

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
         (check-axiom-coloration-4 jg)
         (check-axiom-coloration-uncertainty jg)
         (check-axiom-coloration-inconsistencies jg))))

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

(defn premise
  [jg node]
  (let [stroke (format "_%s" (jgstr node))]
    (exists-just jg [stroke] node)))

(defn add-uncertainty-to-node
  [jg node]
  (-> jg
      (exists-just [:uncertainty-stroke] :uncertainty-node)
      (forall-just [:uncertainty-node] (format "un%s" (jgstr node)))
      (exists-just [(format "un%s" (jgstr node))] node)))

(defn hypothesis
  [jg node]
  (-> jg
      (premise node)
      (add-uncertainty-to-node node)))

(defn can-explain
  [jg explanans explanandum]
  (let [stroke (format "%s_%s" (jgstr explanans) (jgstr explanandum))]
    (-> jg
        (hypothesis explanans)
        (forall-just [explanans] stroke)
        (exists-just [stroke] explanandum))))

(defn assert-color
  [jg stroke-or-node color]
  (when @debugging? (println "asserting" stroke-or-node "as" color))
  (-> jg
      (assoc-in [:coloring stroke-or-node] color)
      (update-in [:graph] graphattr/add-attr stroke-or-node :fillcolor color)
      (update-in [:graph] graphattr/add-attr stroke-or-node :fontcolor (if (= :black color) :white :black))))

(defn assert-black
  [jg stroke-or-node]
  (assert-color jg stroke-or-node :black))

(defn assert-white
  [jg stroke-or-node]
  (assert-color jg stroke-or-node :white))

(defn add-inconsistencies
  "Indicate nodes that are inconsistent with a given node.

  Usage example: (add-inconsistencies jg :node1 [:node4 :node5])"
  [jg node node-inc-set]
  (letfn [(set-inc [jgx n ns] (let [old-inc (get-in jgx [:inconsistent n] #{})]
                                (assoc-in jgx [:inconsistent n] (set/union old-inc (set ns)))))]
    (reduce (fn [jg2 n] (set-inc jg2 n [node]))
            (set-inc jg node node-inc-set) node-inc-set)))

(defn get-inconsistencies
  "Return structure: {:node1 #{:node2 :node3} :node2 #{:node1 :node3} :node3 #{:node1 :node2}}"
  [jg]
  (:inconsistent jg))

(defn spread-white
  [jg]
  (if (check-axioms jg)
    ;; nothing to do, everything checks out
    (do (when @debugging? (println "All axioms satisfied in spread-white."))
        jg)
    ;; something to do (inconsistent), spread white
    (if-let [bad-stroke (first (filter (fn [s] (and (black? jg s)
                                                    (or (some (fn [n] (and (not (uncertainty? n))
                                                                           (white? jg n)))
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
    (let [bad-strokes (filter (fn [s] (and (not (uncertainty? s))
                                           (white? jg s)
                                           (consistent-if-black? jg s)
                                           (or (and (not-empty (jgin jg s))
                                                    (every? (fn [n] (black? jg n))
                                                            (jgin jg s)))
                                               (and (black? jg (first (jgout jg s)))
                                                    (every? (fn [s2] (white? jg s2))
                                                            (jgin jg (first (jgout jg s))))))))
                              (strokes jg))
          bad-nodes (filter (fn [n] (and (not (uncertainty? n))
                                         (white? jg n)
                                         (consistent-if-black? jg n)
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
