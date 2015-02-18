(ns paragon.random-test
  (:require [clojure.test :refer :all]
            [paragon.core :refer :all]
            [clojure.java.io :as io]
            [clojure.data.csv :as csv]
            [loom.graph :as graph]
            [loom.alg :as alg]
            [clojure.math.combinatorics :as combo])
  (:require [taoensso.timbre.profiling :refer (profile defnp)]
            [clojure.set :as set]))

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
        node-groups-cubed (mapcat (fn [[ns1 ns2]] (split-vec (vec (concat ns1 ns2)) chance-split))
                                  node-groups-squared)
        paired (map (fn [ng] (concat ng (if (> chance-and (rand)) [:forall-just] [:exists-just])))
                    node-groups-cubed)
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
                     (recur jg2) jg))
        accessible (alg/pre-traverse (graph/graph (:graph jg-fixed)) (first (shuffle (graph/nodes (:graph jg-fixed)))))]
    #_(prn "accessible:" accessible)
    #_(prn "not-accessible:" (set/difference (set (graph/nodes (:graph jg-fixed)))
                                           (set accessible)))
    #_(prn "nodes" nodes)
    #_(prn "node-groups" (doall node-groups))
    #_(prn "node-groups-squared" (doall node-groups-squared))
    (reduce remove-node-or-stroke
            jg-fixed
            (set/difference (set (graph/nodes (:graph jg-fixed)))
                            (set accessible)))))

(defn count-changes
  [jg1 jg2 ignore]
  (assert (= (:graph jg1) (:graph jg2)))
  (let [bel1 (set (believed jg1))
        bel2 (set (believed jg2))
        ignore-set (set ignore)]
    (count (filter (fn [n] (and (or (and (bel1 n) (not (bel2 n)))
                                    (and (not (bel1 n)) (bel2 n)))
                                (not (ignore-set n))))
                   (nodes jg1)))))

(defn strategy-rand
  [_ bad-strokes bad-nodes]
  (rand-nth (concat bad-strokes bad-nodes)))

(defn strategy-pref-stroke
  [_ bad-strokes bad-nodes]
  (if (empty? bad-strokes) (rand-nth bad-nodes) (rand-nth bad-strokes)))

(defn strategy-pref-node
  [_ bad-strokes bad-nodes]
  (if (empty? bad-nodes) (rand-nth bad-strokes) (rand-nth bad-nodes)))

(defn strategy-pref-fewest-links
  [jg bad-strokes bad-nodes]
  (first (sort-by #(degree jg %) (concat bad-strokes bad-nodes))))

(defn strategy-pref-fewest-links-2
  [jg bad-strokes bad-nodes]
  (first (sort-by (fn [s-or-n] (reduce + (map #(degree jg %)
                                              (concat (graph/incoming (:graph jg) s-or-n)
                                                      (graph/neighbors (:graph jg) s-or-n)))))
                  (concat bad-strokes bad-nodes))))

(defn strategy-pref-most-links
  [jg bad-strokes bad-nodes]
  (last (sort-by #(degree jg %) (concat bad-strokes bad-nodes))))

(defn strategy-pref-most-links-2
  [jg bad-strokes bad-nodes]
  (last (sort-by (fn [s-or-n] (reduce + (map #(degree jg %)
                                              (concat (graph/incoming (:graph jg) s-or-n)
                                                      (graph/neighbors (:graph jg) s-or-n)))))
                  (concat bad-strokes bad-nodes))))

(defn find-black-strategy
  [strat-name]
  (case strat-name
    "rand" strategy-rand
    "pref-stroke" strategy-pref-stroke
    "pref-node" strategy-pref-node
    "fewest" strategy-pref-fewest-links
    "most" strategy-pref-most-links
    "fbmw" strategy-pref-fewest-links
    "mbfw" strategy-pref-most-links
    "degree2" strategy-pref-fewest-links-2))

(defn find-white-strategy
  [strat-name]
  (case strat-name
    "rand" strategy-rand
    "pref-stroke" strategy-pref-stroke
    "pref-node" strategy-pref-node
    "fewest" strategy-pref-fewest-links
    "most" strategy-pref-most-links
    "fbmw" strategy-pref-most-links
    "mbfw" strategy-pref-fewest-links
    "degree2" strategy-pref-most-links-2))

(defn compare-contract-strategies
  []
  (let [strategies ["rand" "pref-stroke" "pref-node" "fewest" "most" "fbmw" "mbfw" "degree2"]
        chances-split [0.7]
        chances-and [0.5]
        cases 1000
        i (atom 0)
        total (* (count chances-split) (count chances-and) cases)]
    (profile
      :debug :compare-contract-strategies
      (doall (apply concat
                    (for [chance-split chances-split
                          chance-and chances-and
                          case (range cases)]
                      (let [jg (gen-random-andor-graph (+ 2 (rand-int 20)) chance-split chance-and)]
                        (swap! i inc)
                        (if (or (empty? (nodes jg)) (> (count (concat (nodes jg) (strokes jg))) 19))
                          []
                          (let [jg-black (reduce (fn [jg n-or-s] (assert-color jg n-or-s :black))
                                                 jg (concat (nodes jg) (strokes jg)))
                                contract-ns [(first (shuffle (nodes jg)))]
                                undecided (filter #(not ((set contract-ns) %)) (concat (nodes jg) (strokes jg)))
                                total-colorings (for [c (combo/selections [:black :white] (count undecided))]
                                                  (partition 2 (interleave undecided c)))
                                _ (if (not-empty (nodes jg)) (println "Colorings:" (count total-colorings)))
                                ;; only works for contraction:
                                total-variations (filter identity
                                                         (for [coloring total-colorings]
                                                           (let [jg-start (reduce (fn [jg n] (assert-color jg n :white))
                                                                                  jg-black contract-ns)
                                                                 jg-new (reduce (fn [jg [n-or-s c]] (assert-color jg n-or-s c))
                                                                                jg-start coloring)]
                                                             (if (check-color-axioms jg-new)
                                                               [jg-new (count-changes jg-black jg-new contract-ns)]))))
                                min-changes (if (not-empty total-variations) (apply min (map second total-variations)))]
                            (println (format "%d/%d" @i total) "contract:" contract-ns "min:" min-changes)
                            (doall (filter
                                     (fn [row] (not= 0 (:Changes row)))
                                     (for [change-type [:contract]
                                           strategy strategies]
                                       (let [time-start (System/nanoTime)
                                             black-strategy (find-black-strategy strategy)
                                             white-strategy (find-white-strategy strategy)
                                             jg-final (contract jg-black
                                                                contract-ns
                                                                :black-strategy black-strategy
                                                                :white-strategy white-strategy)
                                             changes (count-changes jg-black jg-final contract-ns)
                                             change-pct (double (* 100.0 (/ changes (count (nodes jg)))))
                                             time-diff (- (System/nanoTime) time-start)
                                             results {:Strategy     strategy
                                                      :ChangeType   (name change-type)
                                                      :Changes      changes
                                                      :ChangePct    change-pct
                                                      :ChanceAnd    chance-and
                                                      :ChanceSplit  chance-split
                                                      :Case         case
                                                      ;; (changes+1)/(min+1)
                                                      :RatioMin     (double (/ (inc changes) (inc min-changes)))
                                                      :Nodes        (count (nodes jg))
                                                      :Strokes      (count (strokes jg))
                                                      :Microseconds time-diff}]
                                         (println "RatioMin:" (:RatioMin results))
                                         results)))))))))))))

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


