(ns paragon.core
  (:require [clojure.set :as set])
  (:require [clojure.string :as str])
  (:require [loom.graph :as graph])
  (:require [jansi-clj.core :as jansi]))

;;;;
;;;; DEBUGGING
;;;;

(def debugging? (atom false))

(defn turn-on-debugging [] (swap! debugging? (constantly true)))
(defn turn-off-debugging [] (swap! debugging? (constantly false)))

(defmacro with-debugging
  [& body]
  `(do #_(turn-on-debugging)
       (let [result# (do ~@body)]
         #_(turn-off-debugging)
         result#)))

(defn print-msg
  [msgs color]
  (when @debugging?
    (println (color (str/join " " (map (fn [m] (if (sequential? m) (str/join ", " (map str m)) (str m))) msgs))))))

(defn info
  [& msgs]
  (print-msg msgs jansi/yellow))

(defn trace
  [& msgs]
  (print-msg msgs jansi/cyan))

(defn status
  [& msgs]
  (print-msg msgs jansi/blue))

(defn success
  [& msgs]
  (print-msg msgs jansi/green))

(defn warning
  [& msgs]
  (print-msg msgs jansi/red))

(defn error
  [& msgs]
  (print-msg msgs (comp jansi/bold jansi/red)))

;;;;
;;;; PRIMITIVES / DATA STRUCTURES
;;;;

(defn new-fdn
  []
  {:types {}
   :coloring {}
   :priorities {} ;; key = node, val = priority # indicating when changed state
   :observed {} ;; key = node, val = priority # indicating when observed
   :priority-counter 0
   :graph (graph/digraph)})

(defn nodes
  [fdn]
  (map first (filter (fn [[_ t]] (= t :node)) (seq (:types fdn)))))

(defn strokes
  [fdn]
  (map first (filter (fn [[_ t]] (= t :stroke)) (seq (:types fdn)))))

(defn remove-stroke-or-node
  [fdn stroke-or-node]
  (-> fdn
      (update-in [:graph] graph/remove-nodes stroke-or-node)
      (update-in [:types] dissoc stroke-or-node)
      (update-in [:coloring] dissoc stroke-or-node)
      (update-in [:priorities] dissoc stroke-or-node)))

(defn fdnstr
  [stroke-or-node]
  (cond (keyword? stroke-or-node)
        (name stroke-or-node)
        (and (map? stroke-or-node) (:id stroke-or-node))
        (str (:id stroke-or-node))
        (string? stroke-or-node)
        stroke-or-node
        :else
        (pr-str stroke-or-node)))

(defn fdncolor
  [fdn stroke-or-node]
  (get-in fdn [:coloring stroke-or-node] :white))

(defn fdntype
  [fdn stroke-or-node]
  (get-in fdn [:types stroke-or-node]))

(defn white?
  [fdn stroke-or-node]
  (= :white (fdncolor fdn stroke-or-node)))

(defn black?
  [fdn stroke-or-node]
  (= :black (fdncolor fdn stroke-or-node)))

(defn node?
  [fdn stroke-or-node]
  (= :node (fdntype fdn stroke-or-node)))

(defn stroke?
  [fdn stroke-or-node]
  (= :stroke (fdntype fdn stroke-or-node)))

(defn fdnout
  [fdn stroke-or-node]
  (graph/neighbors (:graph fdn) stroke-or-node))

(defn fdnin
  [fdn stroke-or-node]
  (graph/incoming (:graph fdn) stroke-or-node))

(defn fdnpriority
  [fdn stroke-or-node]
  (if (= :bottom stroke-or-node)
    ;; bottom has max priority
    Integer/MAX_VALUE
    (get-in fdn [:priorities stroke-or-node] 0)))

(defn update-priority
  [fdn stroke-or-node]
  (assoc-in fdn [:priorities stroke-or-node] (get fdn :priority-counter)))

(defn inc-priority-counter
  [fdn]
  (update-in fdn [:priority-counter] inc))

(defn is-nondeterministic?
  [fdn stroke-or-node]
  ;; abduction nondeterminism: multiple incoming strokes
  ;; contraction nondeterminism: multiple incoming nodes
  (> (count (fdnin fdn stroke-or-node)) 1))

(defn degree
  [fdn stroke-or-node]
  (+ (graph/in-degree (:graph fdn) stroke-or-node)
     (graph/degree (:graph fdn) stroke-or-node)))

(defn in-degree
  [fdn stroke-or-node]
  (graph/in-degree (:graph fdn) stroke-or-node))

(defn out-degree
  [fdn stroke-or-node]
  (graph/degree (:graph fdn) stroke-or-node))

(defn believed
  "Returns black nodes."
  [fdn]
  (filter (fn [n] (black? fdn n)) (nodes fdn)))

(defn disbelieved
  "Returns white nodes."
  [fdn]
  (filter (fn [n] (white? fdn n)) (nodes fdn)))

(defn nodes-changed
  [fdn1 fdn2]
  (assert (= (:graph fdn1) (:graph fdn2)))
  (let [bel1 (set (believed fdn1))
        bel2 (set (believed fdn2))]
    (filter (fn [n] (or (and (bel1 n) (not (bel2 n)))
                        (and (not (bel1 n)) (bel2 n))))
            (nodes fdn1))))

(defn initial?
  [fdn node]
  (assert (node? fdn node))
  ;; this node has a single stroke that has no incoming nodes
  (and (= 1 (count (fdnin fdn node)))
       (empty? (fdnin fdn (first (fdnin fdn node))))))

;;;;
;;;; CONSTRUCTION
;;;;

(defn forall-just
  [fdn nodes stroke]
  (reduce (fn [fdn2 node]
            (-> fdn2
                (assoc-in [:types node] :node)
                (update-in [:graph] graph/add-edges [node stroke])))
          (assoc-in fdn [:types stroke] :stroke) nodes))

(defn exists-just
  [fdn strokes node]
  (reduce (fn [fdn2 stroke]
            (-> fdn2
                (assoc-in [:types stroke] :stroke)
                (update-in [:graph] graph/add-edges [stroke node])))
          (assoc-in fdn [:types node] :node) strokes))

(defn add-initial
  [fdn & nodes]
  (reduce (fn [fdn2 n]
            (let [stroke (format ".%s" (fdnstr n))]
              (exists-just fdn2 [stroke] n)))
          fdn nodes))

(defn- can-explain-single-hyp
  "Link hyp to explananda via an intermediate stroke."
  [fdn hyp explananda]
  (reduce (fn [fdn2 ev]
            (let [stroke (format "%s->%s" (fdnstr hyp) (fdnstr ev))]
              (-> fdn2
                  (forall-just [hyp] stroke)
                  (exists-just [stroke] ev))))
          fdn explananda))

(defn- can-explain-conjunction-hyp
  "Link each in explanatia to strokes that point to a special conjunction node (one for each explananda),
  which then links to each explananda."
  [fdn explanantia explananda]
  (reduce (fn [fdn2 ev]
            (let [stroke (format "%s->%s" (str/join "&" (map fdnstr explanantia)) (fdnstr ev))
                  fdn-hyps-stroke (forall-just fdn2 explanantia stroke)]
              (exists-just fdn-hyps-stroke [stroke] ev)))
          fdn explananda))

(defn can-explain
  "The explananda, as a conjunction, justify each of the explanantia."
  [fdn explanantia explananda]
  (assert (and (sequential? explanantia) (sequential? explananda)))
  (if (second explanantia)
    (can-explain-conjunction-hyp fdn explanantia explananda)
    (can-explain-single-hyp fdn (first explanantia) explananda)))

(defn add-inconsistencies
  "Indicate nodes that cannot all be simultaneously believed.

  Usage example: (add-inconsistencies fdn [:node1 :node2 :node3] [:node2 :node3] ...)"
  [fdn & nodesets]
  (reduce (fn [fdn2 nodes]
            (let [botstroke (format "bot_%s" (str/join "&" (map fdnstr nodes)))]
              (-> fdn2
                  (forall-just nodes botstroke)
                  (exists-just [botstroke] :bottom))))
          fdn nodesets))

