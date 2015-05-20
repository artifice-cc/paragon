(ns paragon.random-test
  (:require [clojure.test :refer :all]
            [paragon.core :refer :all]
            [paragon.strategies :refer :all]
            [paragon.builders :refer :all]
            [paragon.interfaces :refer :all]
            [paragon.visualization :refer :all]
            [paragon.coloring :refer :all]
            [paragon.axioms :refer :all]
            [clojure.java.io :as io]
            [clojure.data.csv :as csv]
            [loom.graph :as graph]
            [clojure.math.combinatorics :as combo])
  (:require [clojure.set :as set]))

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

(defn compare-contract-strategies-optimal
  []
  (let [strategies ["rand" "min-out-degree" "max-out-degree" "com" "com-mm"]
        chances-split [0.25 0.5 0.75]
        chances-and [0.25 0.5 0.75]
        cases 2000
        i (atom 0)
        total (* (count chances-split) (count chances-and) cases)
        attempted (atom #{})]
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
                                        results)))))))))))))

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
                                                                                                                  (add-initial n)
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
                                     strat-results))))))))))))

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
                                       strat-results)))))))))))))

(defn dump-csv
  [results fname]
  (with-open [wtr (io/writer fname)]
    (csv/write-csv wtr (concat [(sort (map name (keys (first results))))]
                               (map (fn [row] (map second (sort-by (comp name first) (seq row))))
                                    results)))))

(deftest test-gen-random-andor-graph
  (let [random-graphs (doall (for [i (range 20)]
                               (gen-random-andor-graph (+ 2 (rand-int 100)) 0.5 0.5 4)))]
    (is (every? identity (map (fn [jg] (if (check-structure-axioms-debug jg)
                                         true (do (visualize jg) false)))
                              random-graphs)))))
