(ns paragon.strategies
  (:require [paragon.core :refer :all]
            [loom.graph :as graph]
            [loom.alg :as alg]
            [clojure.set :as set]))

(defn spread-abduce-default-strategy
  "Guaranteed that bad-strokes is not empty. Prefers lower priority,
  otherwise prefers lexicographically."
  [fdn bad-strokes]
  (let [best-bad-stroke (first (sort-by (fn [s] [(fdnpriority fdn s) (fdnstr s)])
                                        bad-strokes))]
    (info "Choosing bad stroke:" best-bad-stroke)
    best-bad-stroke))

(defn spread-white-default-strategy
  "Guaranteed that bad-nodes is not empty. Prefers lower priority,
  otherwise prefers lexicographically."
  [fdn bad-nodes]
  (let [best-bad-node (first (sort-by (fn [n] [(fdnpriority fdn n) (fdnstr n)])
                                      bad-nodes))]
    (info "Choosing bad node:" best-bad-node)
    best-bad-node))

(defn strategy-rand
  [_ ns-or-ss]
  (rand-nth ns-or-ss))

(defn strategy-pref-min-out-degree
  [fdn ns-or-ss]
  ;; shuffle first so stable-sort picks random among equal bests
  (first (sort-by #(out-degree fdn %) (shuffle ns-or-ss))))

(defn strategy-pref-max-out-degree
  [fdn ns-or-ss]
  (last (sort-by #(out-degree fdn %) (shuffle ns-or-ss))))

(defn strategy-pref-min-in-degree
  [fdn ns-or-ss]
  (first (sort-by #(in-degree fdn %) (shuffle ns-or-ss))))

(defn strategy-pref-max-in-degree
  [fdn ns-or-ss]
  (last (sort-by #(in-degree fdn %) (shuffle ns-or-ss))))

(def g-transpose
  (memoize (fn [g] (graph/transpose g))))

(def get-ancestors
  (memoize (fn [g n]
             (let [gt (g-transpose g)]
               (alg/post-traverse gt n)))))

(defn strategy-pref-ancestors
  [fdn ns-or-ss min?]
  ;; we know we're only dealing with nodes
  (let [ns (set ns-or-ss)
        n-ancestors (into {} (for [n ns] [n (set (filter #(node? fdn %) (get-ancestors (:graph fdn) n)))]))
        ;; shuffle first so stable-sort picks random among equal bests
        ns-sorted (sort-by #(count (set/intersection ns (get n-ancestors %))) (shuffle (seq ns)))]
    #_(prn n-ancestors)
    #_(prn (map (fn [n] [n (count (set/intersection ns (get n-ancestors n)))]) ns))
    (if min? (first ns-sorted) (last ns-sorted))))

(defn strategy-pref-ancestors-abd
  [fdn ns-or-ss min?]
  ;; we know we're only dealing with strokes
  (let [stroke-ancestor-counts (for [s ns-or-ss]
                                 (let [ns (fdnin fdn s)
                                       anc-counts (sort (map (fn [n] (count (filter #(node? fdn %) (get-ancestors (:graph fdn) n)))) ns))]
                                   [s (if min? (first anc-counts) (last anc-counts))]))
        ss-sorted (sort-by second stroke-ancestor-counts)]
    (if min? (first (first ss-sorted)) (first (last ss-sorted)))))

(defn strategy-pref-min-ancestors-abd-max-in-degree
  [fdn ns-or-ss]
  ;; we know we're only dealing with strokes
  (let [stroke-ancestor-counts (for [s ns-or-ss]
                                 (let [ns (fdnin fdn s)
                                       anc-counts (sort (map (fn [n] (count (filter #(node? fdn %) (get-ancestors (:graph fdn) n)))) ns))]
                                   [s (first anc-counts)]))
        ss-sorted (sort-by second stroke-ancestor-counts)
        min-count (second (first ss-sorted))
        equal-min (map first (take-while (fn [[n c]] (= c min-count)) ss-sorted))]
    (strategy-pref-max-in-degree fdn equal-min)))

(defn strategy-pref-max-in-degree-min-ancestors-abd
  [fdn ns-or-ss]
  ;; we know we're only dealing with strokes
  (let [ss-sorted (reverse (sort-by second (map (fn [n] [n (in-degree fdn n)]) (shuffle ns-or-ss))))
        max-count (second (first ss-sorted))
        equal-max (map first (take-while (fn [[n c]] (= c max-count)) ss-sorted))]
    (strategy-pref-ancestors-abd fdn equal-max true)))

(defn strategy-pref-min-ancestors-abd-min-in-degree
  [fdn ns-or-ss]
  ;; we know we're only dealing with strokes
  (let [stroke-ancestor-counts (for [s ns-or-ss]
                                 (let [ns (fdnin fdn s)
                                       anc-counts (sort (map (fn [n] (count (filter #(node? fdn %) (get-ancestors (:graph fdn) n)))) ns))]
                                   [s (first anc-counts)]))
        ss-sorted (sort-by second stroke-ancestor-counts)
        min-count (second (first ss-sorted))
        equal-min (map first (take-while (fn [[n c]] (= c min-count)) ss-sorted))]
    (strategy-pref-min-in-degree fdn equal-min)))

(defn strategy-pref-min-in-degree-min-ancestors-abd
  [fdn ns-or-ss]
  ;; we know we're only dealing with strokes
  (let [ss-sorted (sort-by second (map (fn [n] [n (in-degree fdn n)]) (shuffle ns-or-ss)))
        min-count (second (first ss-sorted))
        equal-min (map first (take-while (fn [[n c]] (= c min-count)) ss-sorted))]
    (strategy-pref-ancestors-abd fdn equal-min true)))

(defn strategy-pref-min-ancestors-min-in-degree
  [fdn ns-or-ss]
  (let [ns (set (filter #(node? fdn %) ns-or-ss))
        n-ancestors (into {} (for [n ns] [n (set (filter #(node? fdn %) (get-ancestors (:graph fdn) n)))]))
        ;; shuffle first so stable-sort picks random among equal bests
        ns-sorted (sort-by second (map (fn [n] [n (count (set/intersection ns (get n-ancestors n)))]) (shuffle (seq ns))))
        min-count (second (first ns-sorted))
        equal-min (map first (take-while (fn [[n c]] (= c min-count)) ns-sorted))]
    (strategy-pref-min-in-degree fdn equal-min)))

(defn strategy-pref-min-in-degree-min-ancestors
  [fdn ns-or-ss]
  (let [ns-sorted (sort-by second (map (fn [n] [n (in-degree fdn n)]) (shuffle ns-or-ss)))
        min-count (second (first ns-sorted))
        equal-min (map first (take-while (fn [[n c]] (= c min-count)) ns-sorted))]
    (strategy-pref-ancestors fdn equal-min true)))

(defn strategy-pref-min-ancestors-max-in-degree
  [fdn ns-or-ss]
  (let [ns (set (filter #(node? fdn %) ns-or-ss))
        n-ancestors (into {} (for [n ns] [n (set (filter #(node? fdn %) (get-ancestors (:graph fdn) n)))]))
        ;; shuffle first so stable-sort picks random among equal bests
        ns-sorted (sort-by second (map (fn [n] [n (count (set/intersection ns (get n-ancestors n)))]) (shuffle (seq ns))))
        min-count (second (first ns-sorted))
        equal-min (map first (take-while (fn [[n c]] (= c min-count)) ns-sorted))]
    (strategy-pref-max-in-degree fdn equal-min)))

(defn strategy-pref-max-in-degree-min-ancestors
  [fdn ns-or-ss]
  (let [ns-sorted (reverse (sort-by second (map (fn [n] [n (in-degree fdn n)]) (shuffle ns-or-ss))))
        max-count (second (first ns-sorted))
        equal-max (map first (take-while (fn [[n c]] (= c max-count)) ns-sorted))]
    (strategy-pref-ancestors fdn equal-max true)))

(defn find-white-strategy
  [strat-name]
  (case strat-name
    "rand" strategy-rand
    "min-out-degree" strategy-pref-min-out-degree
    "max-out-degree" strategy-pref-max-out-degree
    "min-in-degree" strategy-pref-min-in-degree
    "max-in-degree" strategy-pref-max-in-degree
    "min-ancestors" #(strategy-pref-ancestors %1 %2 true)
    "max-ancestors" #(strategy-pref-ancestors %1 %2 false)
    "min-anc-min-in-deg" strategy-pref-min-ancestors-min-in-degree
    "min-in-deg-min-anc" strategy-pref-min-in-degree-min-ancestors
    "min-anc-max-in-deg" strategy-pref-min-ancestors-max-in-degree
    "max-in-deg-min-anc" strategy-pref-max-in-degree-min-ancestors))

(defn find-abduce-strategy
  [strat-name]
  (case strat-name
    "rand" strategy-rand
    "min-in-degree" strategy-pref-min-in-degree
    "max-in-degree" strategy-pref-max-in-degree
    "min-ancestors" #(strategy-pref-ancestors-abd %1 %2 true)
    "max-ancestors" #(strategy-pref-ancestors-abd %1 %2 false)
    "min-anc-max-in-deg" strategy-pref-min-ancestors-abd-max-in-degree
    "max-in-deg-min-anc" strategy-pref-max-in-degree-min-ancestors-abd
    "min-anc-min-in-deg" strategy-pref-min-ancestors-abd-min-in-degree
    "min-in-deg-min-anc" strategy-pref-min-in-degree-min-ancestors-abd))
