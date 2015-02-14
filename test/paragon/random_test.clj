(ns paragon.random-test
  (:require [clojure.test :refer :all]
            [paragon.core :refer :all]
            [clojure.java.io :as io]
            [clojure.data.csv :as csv]
            [loom.graph :as graph])
  (:require [taoensso.timbre.profiling :refer (profile defnp)]))

(defnp split-vec
  [v chance-split]
  (let [v-count (count v)]
    (if (= 1 v-count)
      [[v]]
      (let [splits (filter (fn [_] (> chance-split (rand))) (range v-count))
            v-groups (doall (filter not-empty (map (fn [i j] (subvec v i j))
                                                   (concat [0] splits)
                                                   (concat splits [v-count]))))]
        #_(prn "v" v "splits" splits "v-groups" v-groups)
        (filter (fn [[v1 v2]] (and (not (empty? v1)) (not (empty? v2))))
                (partition 2 (interleave v-groups (rest v-groups))))))))

(defnp remove-bad-stroke
       [jg]
       (let [ss (strokes jg)
             bad-stroke (first (filter (fn [s] (not (every? (fn [s2] (= s s2))
                                                            ;; find strokes s2 where s2's incoming arrows
                                                            ;; are subseteq of incoming arrows of s
                                                            (filter (fn [s2]
                                                                      (and (not-empty (jgin jg s))
                                                                           (not-empty (jgin jg s2))
                                                                           (every? (set (jgin jg s)) (jgin jg s2))))
                                                                    ;; find strokes that have an arrow to the same node
                                                                    (filter (fn [s2] (= (first (jgout jg s))
                                                                                        (first (jgout jg s2))))
                                                                            ss)))))
                                       ss))]
         (when bad-stroke
           (remove-node-or-stroke jg bad-stroke))))

(defnp gen-random-andor-graph
  [node-count chance-split chance-and]
  (let [nodes (vec (range node-count))
        node-groups (split-vec nodes chance-split)
        node-groups-squared (mapcat (fn [[ns1 ns2]] (split-vec (vec (concat ns1 ns2)) chance-split))
                                    node-groups)
        paired (map (fn [ng] (concat ng (if (> chance-and (rand)) [:forall-just] [:exists-just])))
                    node-groups-squared)
        jg (new-just-graph)
        jg2 (reduce (fn [jg [node-group1 node-group2 linktype]]
                      #_(prn node-group1 node-group2 linktype)
                      (if (= :forall-just linktype)
                        (reduce (fn [jg n] (-> jg (forall-just node-group1 (format "s%s" n))
                                               (exists-just [(format "s%s" n)] n)))
                                jg node-group2)
                        (reduce (fn [jg n1]
                                  (reduce (fn [jg n2]
                                            (-> jg (forall-just [n1] (format "s%s_%s" n1 n2))
                                                (exists-just [(format "s%s_%s" n1 n2)] n2)))
                                          jg node-group2))
                                jg node-group1)))
                    jg paired)
        jg-premises (reduce (fn [jg n] (exists-just jg [(format "s%s" n)] n)) jg2
                            (filter (fn [n] (empty? (graph/incoming (:graph jg2) n)))
                                    (graph/nodes (:graph jg2))))
        ;; find strokes that fail axiom 7
        jg-fixed (loop [jg jg-premises]
                   (if-let [jg2 (remove-bad-stroke jg)]
                     (recur jg2) jg))]
    #_(prn "nodes" nodes)
    #_(prn "node-groups" (doall node-groups))
    #_(prn "node-groups-squared" (doall node-groups-squared))
    jg-fixed))

(defn count-changes
  [jg1 jg2]
  (assert (= (:graph jg1) (:graph jg2)))
  (let [bel1 (set (believed jg1))
        bel2 (set (believed jg2))]
    (count (filter (fn [n] (or (and (bel1 n) (not (bel2 n)))
                               (and (not (bel1 n)) (bel2 n))))
                   (nodes jg1)))))

(defn expand-random
  [jg chance-expand black-strategy white-strategy]
  (let [expandable (filter (fn [_] (> chance-expand (rand))) (nodes jg))]
    (expand jg expandable :black-strategy black-strategy :white-strategy white-strategy)))

(defn contract-random
  [jg chance-contract black-strategy white-strategy]
  (let [contractable (filter (fn [_] (> chance-contract (rand))) (nodes jg))]
    (contract jg contractable :black-strategy black-strategy :white-strategy white-strategy)))

(defn strategy-rand
  [_ bad-strokes bad-nodes]
  (rand-nth (concat bad-strokes bad-nodes)))

(defn strategy-pref-stroke
  [_ bad-strokes bad-nodes]
  (if (empty? bad-strokes) (rand-nth bad-nodes) (rand-nth bad-strokes)))

(defn strategy-pref-node
  [_ bad-strokes bad-nodes]
  (if (empty? bad-nodes) (rand-nth bad-strokes) (rand-nth bad-nodes)))

(defn find-black-strategy
  [strat-name]
  (case strat-name
    "default" strategy-rand
    "pref-stroke" strategy-pref-stroke
    "pref-node" strategy-pref-node))

(defn find-white-strategy
  [strat-name]
  (case strat-name
    "default" strategy-rand
    "pref-stroke" strategy-pref-stroke
    "pref-node" strategy-pref-node))

(defn compare-expand-strategies
  []
  (let [strategies ["default" "pref-stroke" "pref-node"]
        chances-split [0.25 0.50 0.75]
        chances-expand-contract [0.02 0.04 0.06 0.08 0.10]
        chances-and [0.0 0.25 0.5 0.75 1.0]
        cases 100
        i (atom 0)
        total (* (count chances-split) (count chances-expand-contract) (count chances-and) cases)]
    (profile
      :debug :compare-expand-strategies
      (doall (apply concat
                    (for [chance-split chances-split
                          chance-expand-contract chances-expand-contract
                          chance-and chances-and
                          case (range cases)]
                      (let [jg (gen-random-andor-graph (+ 2 (rand-int 100)) chance-split chance-and)]
                        (swap! i inc)
                        (prn (format "%d/%d" @i total))
                        (if (empty? (nodes jg))
                          []
                          (for [strategy strategies
                                change-type [:expand :contract]]
                            (let [time-start (System/nanoTime)
                                  changes (if (= :expand change-type)
                                            (let [jg-new (expand-random jg chance-expand-contract
                                                                        (find-black-strategy strategy)
                                                                        (find-white-strategy strategy))]
                                              (count-changes jg jg-new))
                                            (let [jg-black (reduce assert-black jg (concat (strokes jg) (nodes jg)))
                                                  jg-new (contract-random jg-black chance-expand-contract
                                                                          (find-black-strategy strategy)
                                                                          (find-white-strategy strategy))]
                                              (count-changes jg-black jg-new)))
                                  change-pct (double (* 100.0 (/ changes (count (nodes jg)))))
                                  time-diff (- (System/nanoTime) time-start)]
                              {:ChanceSplit  chance-split :ChanceExpandContract chance-expand-contract :ChanceAnd chance-and
                               :Strategy     strategy :ChangeType (name change-type)
                               :Case         case :ChangePct change-pct :Nodes (count (nodes jg)) :Strokes (count (strokes jg))
                               :Microseconds time-diff}))))))))))

(defn dump-csv
  [results fname]
  (with-open [wtr (io/writer fname)]
    (csv/write-csv wtr (concat [(sort (map name (keys (first results))))]
                               (map (fn [row] (map second (sort-by (comp name first) (seq row))))
                                    results)))))

(deftest test-gen-random-andor-graph
  (let [random-graphs (profile :debug :gen-random-andor-graph
                               (doall (for [i (range 20)]
                                        (gen-random-andor-graph (+ 2 (rand-int 100)) 0.5 0.5))))]
    (is (profile :debug :check-structure-axioms
                 (every? identity (map (fn [jg] (if (check-structure-axioms-debug jg)
                                                  true (do (visualize jg) false)))
                                       random-graphs))))))


