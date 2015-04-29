(ns paragon.random-test
  (:require [clojure.test :refer :all]
            [paragon.core :refer :all]
            [clojure.java.io :as io]
            [clojure.data.csv :as csv]
            [loom.graph :as graph]
            [loom.alg :as alg]
            [clojure.math.combinatorics :as combo])
  (:require [taoensso.timbre.profiling :refer (profile defnp p)]
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
             bad-stroke (first (filter (fn [s] (some (fn [s2]
                                                       (and (not= s s2)
                                                            ;; find strokes s2 that have an arrow
                                                            ;; to the same node
                                                            (= (first (jgout jg s))
                                                               (first (jgout jg s2)))
                                                            ;; and where s2's incoming arrows
                                                            ;; are subseteq of incoming arrows of s
                                                            (not-empty (jgin jg s))
                                                            (not-empty (jgin jg s2))
                                                            (every? (set (jgin jg s)) (jgin jg s2))))
                                                     ss))
                                       ss))]
         (when bad-stroke
           (remove-node-or-stroke jg bad-stroke))))

(defnp remove-inaccessible
  [jg]
  (let [accessible (p :gen-random-andor-graph/traverse
                      (set (alg/pre-traverse (graph/graph (:graph jg)) (first (shuffle (graph/nodes (:graph jg)))))))]
    (reduce remove-node-or-stroke jg (filter #(not (accessible %)) (graph/nodes (:graph jg))))))

(defnp gen-random-andor-graph
  [node-count chance-split chance-and inconsistent-count]
  (let [node-options (vec (map str (range node-count)))
        node-groups (split-vec node-options chance-split)
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
        top-nodes (filter (fn [n] (empty? (graph/incoming (:graph jg2) n)))
                          (nodes jg2))
        jg-premises (reduce (fn [jg n] (exists-just jg [(format "s%s" n)] n))
                            jg2 top-nodes)
        jg-inconsistencies (apply add-inconsistencies jg-premises
                                  (take inconsistent-count
                                        (shuffle (for [n1 (nodes jg-premises)
                                                       n2 (shuffle (nodes jg-premises))
                                                       :when (not= n1 n2)]
                                                   [n1 n2]))))
        jg-accessible (remove-inaccessible jg-inconsistencies)
        ;; find strokes that fail axiom 7
        jg-fixed (p :gen-random-andor-graph/fixed
                    (loop [jg jg-accessible]
                      (if-let [jg2 (remove-bad-stroke jg)]
                        (recur jg2) jg)))]
    (remove-inaccessible jg-fixed)))

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
  [_ ns-or-ss]
  (rand-nth ns-or-ss))

(defn strategy-pref-min-out-degree
  [jg ns-or-ss]
  ;; shuffle first so stable-sort picks random among equal bests
  (first (sort-by #(out-degree jg %) (shuffle ns-or-ss))))

(defn strategy-pref-max-out-degree
  [jg ns-or-ss]
  (last (sort-by #(out-degree jg %) (shuffle ns-or-ss))))

(defn strategy-pref-min-in-degree
  [jg ns-or-ss]
  (first (sort-by #(in-degree jg %) (shuffle ns-or-ss))))

(defn strategy-pref-max-in-degree
  [jg ns-or-ss]
  (last (sort-by #(in-degree jg %) (shuffle ns-or-ss))))

(def g-transpose
  (memoize (fn [g] (graph/transpose g))))

(def get-ancestors
  (memoize (fn [g n]
             (let [gt (g-transpose g)]
               (alg/post-traverse gt n)))))

(defn strategy-pref-ancestors
  [jg ns-or-ss min?]
  ;; we know we're only dealing with nodes
  (let [ns (set ns-or-ss)
        n-ancestors (into {} (for [n ns] [n (set (filter #(node? jg %) (get-ancestors (:graph jg) n)))]))
        ;; shuffle first so stable-sort picks random among equal bests
        ns-sorted (sort-by #(count (set/intersection ns (get n-ancestors %))) (shuffle (seq ns)))]
    #_(prn n-ancestors)
    #_(prn (map (fn [n] [n (count (set/intersection ns (get n-ancestors n)))]) ns))
    (if min? (first ns-sorted) (last ns-sorted))))

(defn strategy-pref-ancestors-abd
  [jg ns-or-ss min?]
  ;; we know we're only dealing with strokes
  (let [stroke-ancestor-counts (for [s ns-or-ss]
                                 (let [ns (jgin jg s)
                                       anc-counts (sort (map (fn [n] (count (filter #(node? jg %) (get-ancestors (:graph jg) n)))) ns))]
                                   [s (if min? (first anc-counts) (last anc-counts))]))
        ss-sorted (sort-by second stroke-ancestor-counts)]
    (if min? (first (first ss-sorted)) (first (last ss-sorted)))))

(defn strategy-pref-min-ancestors-abd-max-in-degree
  [jg ns-or-ss]
  ;; we know we're only dealing with strokes
  (let [stroke-ancestor-counts (for [s ns-or-ss]
                                 (let [ns (jgin jg s)
                                       anc-counts (sort (map (fn [n] (count (filter #(node? jg %) (get-ancestors (:graph jg) n)))) ns))]
                                   [s (first anc-counts)]))
        ss-sorted (sort-by second stroke-ancestor-counts)
        min-count (second (first ss-sorted))
        equal-min (map first (take-while (fn [[n c]] (= c min-count)) ss-sorted))]
    (strategy-pref-max-in-degree jg equal-min)))

(defn strategy-pref-max-in-degree-min-ancestors-abd
  [jg ns-or-ss]
  ;; we know we're only dealing with strokes
  (let [ss-sorted (reverse (sort-by second (map (fn [n] [n (in-degree jg n)]) (shuffle ns-or-ss))))
        max-count (second (first ss-sorted))
        equal-max (map first (take-while (fn [[n c]] (= c max-count)) ss-sorted))]
    (strategy-pref-ancestors-abd jg equal-max true)))

(defn strategy-pref-min-ancestors-abd-min-in-degree
  [jg ns-or-ss]
  ;; we know we're only dealing with strokes
  (let [stroke-ancestor-counts (for [s ns-or-ss]
                                 (let [ns (jgin jg s)
                                       anc-counts (sort (map (fn [n] (count (filter #(node? jg %) (get-ancestors (:graph jg) n)))) ns))]
                                   [s (first anc-counts)]))
        ss-sorted (sort-by second stroke-ancestor-counts)
        min-count (second (first ss-sorted))
        equal-min (map first (take-while (fn [[n c]] (= c min-count)) ss-sorted))]
    (strategy-pref-min-in-degree jg equal-min)))

(defn strategy-pref-min-in-degree-min-ancestors-abd
  [jg ns-or-ss]
  ;; we know we're only dealing with strokes
  (let [ss-sorted (sort-by second (map (fn [n] [n (in-degree jg n)]) (shuffle ns-or-ss)))
        min-count (second (first ss-sorted))
        equal-min (map first (take-while (fn [[n c]] (= c min-count)) ss-sorted))]
    (strategy-pref-ancestors-abd jg equal-min true)))

(defn strategy-pref-min-ancestors-min-in-degree
  [jg ns-or-ss]
  (let [ns (set (filter #(node? jg %) ns-or-ss))
        n-ancestors (into {} (for [n ns] [n (set (filter #(node? jg %) (get-ancestors (:graph jg) n)))]))
        ;; shuffle first so stable-sort picks random among equal bests
        ns-sorted (sort-by second (map (fn [n] [n (count (set/intersection ns (get n-ancestors n)))]) (shuffle (seq ns))))
        min-count (second (first ns-sorted))
        equal-min (map first (take-while (fn [[n c]] (= c min-count)) ns-sorted))]
    (strategy-pref-min-in-degree jg equal-min)))

(defn strategy-pref-min-in-degree-min-ancestors
  [jg ns-or-ss]
  (let [ns-sorted (sort-by second (map (fn [n] [n (in-degree jg n)]) (shuffle ns-or-ss)))
        min-count (second (first ns-sorted))
        equal-min (map first (take-while (fn [[n c]] (= c min-count)) ns-sorted))]
    (strategy-pref-ancestors jg equal-min true)))

(defn strategy-pref-min-ancestors-max-in-degree
  [jg ns-or-ss]
  (let [ns (set (filter #(node? jg %) ns-or-ss))
        n-ancestors (into {} (for [n ns] [n (set (filter #(node? jg %) (get-ancestors (:graph jg) n)))]))
        ;; shuffle first so stable-sort picks random among equal bests
        ns-sorted (sort-by second (map (fn [n] [n (count (set/intersection ns (get n-ancestors n)))]) (shuffle (seq ns))))
        min-count (second (first ns-sorted))
        equal-min (map first (take-while (fn [[n c]] (= c min-count)) ns-sorted))]
    (strategy-pref-max-in-degree jg equal-min)))

(defn strategy-pref-max-in-degree-min-ancestors
  [jg ns-or-ss]
  (let [ns-sorted (reverse (sort-by second (map (fn [n] [n (in-degree jg n)]) (shuffle ns-or-ss))))
        max-count (second (first ns-sorted))
        equal-max (map first (take-while (fn [[n c]] (= c max-count)) ns-sorted))]
    (strategy-pref-ancestors jg equal-max true)))

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

(defn compare-contract-strategies-optimal
  []
  (let [strategies ["rand" "min-out-degree" "max-out-degree" "com" "com-mm"]
        chances-split [0.25 0.5 0.75]
        chances-and [0.25 0.5 0.75]
        cases 2000
        i (atom 0)
        total (* (count chances-split) (count chances-and) cases)
        attempted (atom #{})]
    (profile
      :debug :compare-contract-strategies
      (doall (apply concat
                    (for [chance-split chances-split
                          chance-and chances-and
                          case (range cases)]
                      (let [jg (gen-random-andor-graph (+ 2 (rand-int 50)) chance-split chance-and 0)]
                        (swap! i inc)
                        (if (or (@attempted jg) (empty? (nodes jg)) (> (count (concat (nodes jg) (strokes jg))) 19))
                          []
                          (do
                            (swap! attempted conj jg)
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
                              (println (format "%d/%d" @i total) "chance-and" chance-and "chance-split" chance-split "contract:" contract-ns "min:" min-changes)
                              (doall (filter
                                       (fn [row] (not= 0 (:Changes row)))
                                       (for [change-type [:contract]
                                             strategy strategies]
                                         (let [time-start (System/nanoTime)
                                               jg-final (cond (= strategy "com")
                                                              (process-with-com jg contract-ns false)
                                                              (= strategy "com-mm")
                                                              (process-with-com jg contract-ns true)
                                                              :else
                                                              (contract jg-black
                                                                        contract-ns
                                                                        :white-strategy (find-white-strategy strategy)))
                                               changes (count-changes jg-black jg-final contract-ns)
                                               change-pct (double (* 100.0 (/ changes (- (count (nodes jg))
                                                                                         (count contract-ns)))))
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
                                           results))))))))))))))

(comment
  (doall (take (rand-int (count non-bottom-leaf-nodes))
               (shuffle non-bottom-leaf-nodes))))

(defn compare-contract-strategies
  []
  (let [strategies ["rand" "max-in-degree" "min-in-degree" "min-out-degree" "max-out-degree" "min-ancestors" "max-ancestors" "min-anc-min-in-deg" "min-in-deg-min-anc" "min-anc-max-in-deg" "max-in-deg-min-anc" "com"] ;; "com-mm"
        chances-split [0.25]
        chances-and [0.75]
        ;; don't use inconsistencies since it's hard to make a mostly-black but consistent starting jg
        inconsistent-counts [0]
        cases 5000
        i (atom 0)
        total (* (count chances-split) (count chances-and) (count inconsistent-counts) cases)
        attempted (atom #{})]
    (profile
      :debug :compare-contract-strategies
      (doall (apply concat
                    (for [chance-split chances-split
                          chance-and chances-and
                          inconsistent-count inconsistent-counts
                          case (range cases)]
                      (let [jg (gen-random-andor-graph (+ 2 (rand-int 300)) chance-split chance-and inconsistent-count)]
                        (swap! i inc)
                        (if (or (@attempted jg) (empty? (nodes jg)))
                          []
                          (do
                            (swap! attempted conj jg)
                            (let [jg-black (reduce (fn [jg n-or-s] (assert-color jg n-or-s :black))
                                                   jg (concat (nodes jg) (strokes jg)))
                                  non-bottom-leaf-nodes (filter #(and (not= :bottom %)
                                                                      (empty? (graph/neighbors (:graph jg-black) %)))
                                                                (nodes jg-black))
                                  non-bottom-nodes (filter #(not= :bottom %)
                                                           (nodes jg-black))
                                  contract-ns [(first (shuffle non-bottom-nodes))]]
                              (if (not-empty contract-ns)
                                (let [strat-results (doall (filter
                                                            (fn [row] (and (not= 0 (:Changes row))
                                                                           (not (nil? (:RecoversPct row)))))
                                                             (for [change-type [:contract]
                                                                   strategy strategies]
                                                               (let [time-start (System/nanoTime)
                                                                     jg-final (cond (= strategy "com")
                                                                                    (process-with-com jg contract-ns false)
                                                                                    (= strategy "com-mm")
                                                                                    (process-with-com jg contract-ns true)
                                                                                    :else
                                                                                    (contract jg-black
                                                                                              contract-ns
                                                                                              :white-strategy (find-white-strategy strategy)))
                                                                     time-diff (- (System/nanoTime) time-start)
                                                                     changes (count-changes jg-black jg-final [])
                                                                     change-pct (double (* 100.0 (/ changes (count (nodes jg)))))
                                                                     contract-ns-set (set contract-ns)
                                                                     whitened (filter (fn [n] (and (not (contract-ns-set n))
                                                                                                   (white? jg-final n)))
                                                                                      (nodes jg-final))
                                                                     recovers (doall (filter (fn [n]
                                                                                               (let [jg-expanded (-> jg-final
                                                                                                                     (premise n)
                                                                                                                     (assert-black (format ".%s" (jgstr n)))
                                                                                                                     (spread-black))]
                                                                                                 (every? #(black? jg-expanded %) contract-ns)))
                                                                                             whitened))
                                                                     recovers-pct (when (not-empty whitened)
                                                                                    (double (* 100.0 (/ (count recovers) (count whitened)))))
                                                                     ;changes (count-changes jg-black jg-final contract-ns)
                                                                     ;change-pct (double (* 100.0 (/ changes (- (count (nodes jg))
                                                                     ;                                          (count contract-ns)))))
                                                                     results {:Strategy     strategy
                                                                              :ChangeType   (name change-type)
                                                                              :Changes      changes
                                                                              :ChangePct    change-pct
                                                                              :RecoversPct  recovers-pct
                                                                              :ChanceAnd    chance-and
                                                                              :ChanceSplit  chance-split
                                                                              :Inconsistent inconsistent-count
                                                                              :Case         case
                                                                              :Nodes        (count (nodes jg))
                                                                              :Strokes      (count (strokes jg))
                                                                              :Microseconds time-diff
                                                                              :JGFinal      jg-final}]
                                                                 #_(visualize jg-final)
                                                                 (println strategy "\tnodes:" (count (nodes jg)) "\tchanges:" changes "\trecovers-pct:" recovers-pct)
                                                                 results))))
                                      min-changes (if (not-empty strat-results) (apply min (map :Changes strat-results)))]
                                  (println (format "%d/%d" @i total) "chance-and" chance-and
                                           "chance-split" chance-split "contract:" contract-ns "min:" min-changes)
                                  (map (fn [results] (-> results
                                                         (dissoc :JGFinal)
                                                         (assoc :RatioMin ;; (changes+1)/(min+1)
                                                                (double (/ (inc (:Changes results))
                                                                           (inc min-changes)))
                                                                :Same (>= 1 (count (set (map :JGFinal strat-results)))))))
                                       strat-results)))))))))))))

(defn compare-abduce-contract-strategies
  []
  (let [abduce-strategies ["rand" "min-in-degree" "max-in-degree" "min-ancestors" "max-ancestors" "min-anc-max-in-deg" "max-in-deg-min-anc" "min-anc-min-in-deg" "min-in-deg-min-anc"]
        contract-strategies ["min-ancestors"]
        chances-split [0.25]
        chances-and [0.75]
        inconsistent-counts [0 2 4 6 8 10 12]
        cases 500
        i (atom 0)
        total (* (count chances-split) (count chances-and) (count inconsistent-counts) cases)
        attempted (atom #{})]
    (profile
      :debug :compare-abduce-contract-strategies
      (doall
        (apply concat
               (filter identity
                       (for [chance-split chances-split
                             chance-and chances-and
                             inconsistent-count inconsistent-counts
                             case (range cases)]
                         (let [jg (gen-random-andor-graph (+ 2 (rand-int 300)) chance-split chance-and inconsistent-count)]
                           (swap! i inc)
                           (if (or (@attempted jg) (empty? (nodes jg)))
                             []
                             (do
                               (swap! attempted conj jg)
                               (let [non-bottom-nodes (filter #(not= :bottom %) (nodes jg))
                                     abduce-ns [(first (shuffle non-bottom-nodes))]]
                                 (if (not-empty abduce-ns)
                                   (let [strat-results (doall (for [abduce-strategy abduce-strategies
                                                                    white-strategy contract-strategies]
                                                                (let [time-start (System/nanoTime)
                                                                      jg-final (abduce jg
                                                                                       abduce-ns
                                                                                       :abduce-strategy (find-abduce-strategy abduce-strategy)
                                                                                       :white-strategy (find-white-strategy white-strategy))
                                                                      time-diff (- (System/nanoTime) time-start)
                                                                      explained (filter #(black? jg-final %) abduce-ns)
                                                                      changes (count-changes jg jg-final explained)
                                                                      change-pct (double (* 100.0 (/ changes (count (nodes jg)))))
                                                                      ;changes (count-changes jg jg-final abduce-ns)
                                                                      ;change-pct (double (* 100.0 (/ changes (- (count (nodes jg))
                                                                      ;                                          (count abduce-ns)))))
                                                                      explained-pct (double (* 100.0 (/ (count explained) (count abduce-ns))))
                                                                      results {:AbduceStrategy abduce-strategy
                                                                               :WhiteStrategy  white-strategy
                                                                               :Strategy       (format "%s_%s"
                                                                                                       abduce-strategy
                                                                                                       white-strategy)
                                                                               :Changes        changes
                                                                               :ChangePct      change-pct
                                                                               :Explained      (count explained)
                                                                               :ExplainedPct   explained-pct
                                                                               :ChanceAnd      chance-and
                                                                               :ChanceSplit    chance-split
                                                                               :Inconsistent   inconsistent-count
                                                                               :Case           case
                                                                               :Nodes          (count (nodes jg))
                                                                               :Strokes        (count (strokes jg))
                                                                               :Microseconds   time-diff
                                                                               :JGFinal        jg-final}]
                                                                  (println "\tabduce" abduce-strategy "white" white-strategy
                                                                           "changes:" changes "changepct:" change-pct
                                                                           "inconsistent:" inconsistent-count
                                                                           "explained:" (count explained) "explainedpct:" explained-pct)
                                                                  results)))
                                         min-changes (if (not-empty strat-results) (apply min (map :Changes strat-results)))
                                         max-explained (if (not-empty strat-results) (apply max (map :Explained strat-results)))]
                                     (println (format "%d/%d" @i total) "chance-and" chance-and "chance-split" chance-split
                                              "abduce count:" (count abduce-ns) "min-changes:" min-changes "max-explained:" max-explained)
                                     (map (fn [results] (-> results
                                                            (dissoc :JGFinal)
                                                            (assoc :ChangedRatioMin ;; (changes+1)/(min+1)
                                                                   (double (/ (inc (:Changes results))
                                                                              (inc min-changes)))
                                                                   :ExplainedRatioMax
                                                                   (double (/ (inc (:Explained results))
                                                                              (inc max-explained)))
                                                                   :Same (>= 1 (count (set (map :JGFinal strat-results)))))))
                                          strat-results))))))))))))))

(defn dump-csv
  [results fname]
  (with-open [wtr (io/writer fname)]
    (csv/write-csv wtr (concat [(sort (map name (keys (first results))))]
                               (map (fn [row] (map second (sort-by (comp name first) (seq row))))
                                    results)))))

(deftest test-gen-random-andor-graph
  (let [random-graphs (profile :debug :gen-random-andor-graph
                               (doall (for [i (range 20)]
                                        (gen-random-andor-graph (+ 2 (rand-int 100)) 0.5 0.5 4))))]
    (is (profile :debug :check-structure-axioms
                 (every? identity (map (fn [jg] (if (check-structure-axioms-debug jg)
                                                  true (do (visualize jg) false)))
                                       random-graphs))))))
