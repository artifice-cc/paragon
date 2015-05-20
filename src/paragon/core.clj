(ns paragon.core
  (:require [clojure.string :as str])
  (:require [loom.graph :as graph]))

;;;;
;;;; DEBUGGING
;;;;

(def debugging? (atom false))

(defn turn-on-debugging [] (swap! debugging? (constantly true)))
(defn turn-off-debugging [] (swap! debugging? (constantly false)))

;;;;
;;;; PRIMITIVES / DATA STRUCTURES
;;;;

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

(defn jgstr
  [stroke-or-node]
  (cond (keyword? stroke-or-node)
        (name stroke-or-node)
        (and (map? stroke-or-node) (:id stroke-or-node))
        (str (:id stroke-or-node))
        :else
        (pr-str stroke-or-node)))

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

(defn initial?
  [jg node]
  (assert (node? jg node))
  ;; this node has a single stroke that has no incoming nodes
  (and (= 1 (count (jgin jg node)))
       (empty? (jgin jg (first (jgin jg node))))))

;;;;
;;;; CONSTRUCTION
;;;;

(defn forall-just
  [jg nodes stroke]
  (reduce (fn [jg2 node]
            (-> jg2
                (assoc-in [:types node] :node)
                (update-in [:graph] graph/add-edges [node stroke])))
          (assoc-in jg [:types stroke] :stroke) nodes))

(defn exists-just
  [jg strokes node]
  (reduce (fn [jg2 stroke]
            (-> jg2
                (assoc-in [:types stroke] :stroke)
                (update-in [:graph] graph/add-edges [stroke node])))
          (assoc-in jg [:types node] :node) strokes))

(defn add-initial
  [jg & nodes]
  (reduce (fn [jg2 n]
            (let [stroke (format ".%s" (jgstr n))]
              (exists-just jg2 [stroke] n)))
          jg nodes))

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

(defn can-explain
  "The explananda, as a conjunction, justify each of the explanantia."
  [jg explanantia explananda]
  (assert (and (sequential? explanantia) (sequential? explananda)))
  (if (second explanantia)
    (can-explain-conjunction-hyp jg explanantia explananda)
    (can-explain-single-hyp jg (first explanantia) explananda)))

(defn add-inconsistencies
  "Indicate nodes that cannot all be simultaneously believed.

  Usage example: (add-inconsistencies jg [:node1 :node2 :node3] [:node2 :node3] ...)"
  [jg & nodesets]
  (reduce (fn [jg2 nodes]
            (let [botstroke (format "bot_%s" (str/join "-" (map jgstr nodes)))]
              (-> jg2
                  (forall-just nodes botstroke)
                  (exists-just [botstroke] :bottom))))
          jg nodesets))

