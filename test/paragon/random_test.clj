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
  [fdn1 fdn2 ignore]
  (assert (= (:graph fdn1) (:graph fdn2)))
  (let [bel1 (set (believed fdn1))
        bel2 (set (believed fdn2))
        ignore-set (set ignore)]
    (count (filter (fn [n] (and (or (and (bel1 n) (not (bel2 n)))
                                    (and (not (bel1 n)) (bel2 n)))
                                (not (ignore-set n))))
                   (nodes fdn1)))))

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
                    (let [fdn (gen-random-andor-graph (+ 2 (rand-int 50)) chance-split chance-and 0)]
                      (swap! i inc)
                      (if (or (@attempted fdn) (empty? (nodes fdn)) (> (count (concat (nodes fdn) (strokes fdn))) 19))
                        []
                        (do
                          (swap! attempted conj fdn)
                          (let [fdn-black (reduce (fn [fdn n-or-s] (assert-color fdn n-or-s :black))
                                                 fdn (concat (nodes fdn) (strokes fdn)))
                                contract-ns [(first (shuffle (nodes fdn)))]
                                undecided (filter #(not ((set contract-ns) %)) (concat (nodes fdn) (strokes fdn)))
                                total-colorings (for [c (combo/selections [:black :white] (count undecided))]
                                                  (partition 2 (interleave undecided c)))
                                _ (if (not-empty (nodes fdn)) (println "Colorings:" (count total-colorings)))
                                ;; only works for contraction:
                                total-variations (filter identity
                                                         (for [coloring total-colorings]
                                                           (let [fdn-start (reduce (fn [fdn n] (assert-color fdn n :white))
                                                                                  fdn-black contract-ns)
                                                                 fdn-new (reduce (fn [fdn [n-or-s c]] (assert-color fdn n-or-s c))
                                                                                fdn-start coloring)]
                                                             (if (check-color-axioms fdn-new)
                                                               [fdn-new (count-changes fdn-black fdn-new contract-ns)]))))
                                min-changes (if (not-empty total-variations) (apply min (map second total-variations)))]
                            (println (format "%d/%d" @i total) "chance-and" chance-and "chance-split" chance-split "contract:" contract-ns "min:" min-changes)
                            (doall (filter
                                    (fn [row] (not= 0 (:Changes row)))
                                    (for [change-type [:contract]
                                          strategy strategies]
                                      (let [time-start (System/nanoTime)
                                            fdn-final (cond (= strategy "com")
                                                           (process-with-com fdn contract-ns false)
                                                           (= strategy "com-mm")
                                                           (process-with-com fdn contract-ns true)
                                                           :else
                                                           (contract fdn-black
                                                                     contract-ns
                                                                     :white-strategy (find-white-strategy strategy)))
                                            changes (count-changes fdn-black fdn-final contract-ns)
                                            change-pct (double (* 100.0 (/ changes (- (count (nodes fdn))
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
                                                     :Nodes        (count (nodes fdn))
                                                     :Strokes      (count (strokes fdn))
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
        ;; don't use inconsistencies since it's hard to make a mostly-black but consistent starting fdn
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
                    (let [fdn (gen-random-andor-graph (+ 2 (rand-int 300)) chance-split chance-and inconsistent-count)]
                      (swap! i inc)
                      (if (or (@attempted fdn) (empty? (nodes fdn)))
                        []
                        (do
                          (swap! attempted conj fdn)
                          (let [fdn-black (reduce (fn [fdn n-or-s] (assert-color fdn n-or-s :black))
                                                 fdn (concat (nodes fdn) (strokes fdn)))
                                non-bottom-leaf-nodes (filter #(and (not= :bottom %)
                                                                    (empty? (graph/neighbors (:graph fdn-black) %)))
                                                              (nodes fdn-black))
                                non-bottom-nodes (filter #(not= :bottom %)
                                                         (nodes fdn-black))
                                contract-ns [(first (shuffle non-bottom-nodes))]]
                            (if (not-empty contract-ns)
                              (let [strat-results (doall (filter
                                                          (fn [row] (and (not= 0 (:Changes row))
                                                                         (not (nil? (:RecoversPct row)))))
                                                          (for [change-type [:contract]
                                                                strategy strategies]
                                                            (let [time-start (System/nanoTime)
                                                                  fdn-final (cond (= strategy "com")
                                                                                 (process-with-com fdn contract-ns false)
                                                                                 (= strategy "com-mm")
                                                                                 (process-with-com fdn contract-ns true)
                                                                                 :else
                                                                                 (contract fdn-black
                                                                                           contract-ns
                                                                                           :white-strategy (find-white-strategy strategy)))
                                                                  time-diff (- (System/nanoTime) time-start)
                                                                  changes (count-changes fdn-black fdn-final [])
                                                                  change-pct (double (* 100.0 (/ changes (count (nodes fdn)))))
                                                                  contract-ns-set (set contract-ns)
                                                                  whitened (filter (fn [n] (and (not (contract-ns-set n))
                                                                                                (white? fdn-final n)))
                                                                                   (nodes fdn-final))
                                                                  recovers (doall (filter (fn [n]
                                                                                            (let [fdn-expanded (-> fdn-final
                                                                                                                  (add-initial n)
                                                                                                                  (assert-black (format ".%s" (fdnstr n)))
                                                                                                                  (spread-black))]
                                                                                              (every? #(black? fdn-expanded %) contract-ns)))
                                                                                          whitened))
                                                                  recovers-pct (when (not-empty whitened)
                                                                                 (double (* 100.0 (/ (count recovers) (count whitened)))))
                                        ;changes (count-changes fdn-black fdn-final contract-ns)
                                        ;change-pct (double (* 100.0 (/ changes (- (count (nodes fdn))
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
                                                                           :Nodes        (count (nodes fdn))
                                                                           :Strokes      (count (strokes fdn))
                                                                           :Microseconds time-diff
                                                                           :FDNFinal      fdn-final}]
                                                              #_(visualize fdn-final)
                                                              (println strategy "\tnodes:" (count (nodes fdn)) "\tchanges:" changes "\trecovers-pct:" recovers-pct)
                                                              results))))
                                    min-changes (if (not-empty strat-results) (apply min (map :Changes strat-results)))]
                                (println (format "%d/%d" @i total) "chance-and" chance-and
                                         "chance-split" chance-split "contract:" contract-ns "min:" min-changes)
                                (map (fn [results] (-> results
                                                       (dissoc :FDNFinal)
                                                       (assoc :RatioMin ;; (changes+1)/(min+1)
                                                              (double (/ (inc (:Changes results))
                                                                         (inc min-changes)))
                                                              :Same (>= 1 (count (set (map :FDNFinal strat-results)))))))
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
                      (let [fdn (gen-random-andor-graph (+ 2 (rand-int 300)) chance-split chance-and inconsistent-count)]
                        (swap! i inc)
                        (if (or (@attempted fdn) (empty? (nodes fdn)))
                          []
                          (do
                            (swap! attempted conj fdn)
                            (let [non-bottom-nodes (filter #(not= :bottom %) (nodes fdn))
                                  abduce-ns [(first (shuffle non-bottom-nodes))]]
                              (if (not-empty abduce-ns)
                                (let [strat-results (doall (for [abduce-strategy abduce-strategies
                                                                 white-strategy contract-strategies]
                                                             (let [time-start (System/nanoTime)
                                                                   fdn-final (abduce fdn
                                                                                    abduce-ns
                                                                                    :abduce-strategy (find-abduce-strategy abduce-strategy)
                                                                                    :white-strategy (find-white-strategy white-strategy))
                                                                   time-diff (- (System/nanoTime) time-start)
                                                                   explained (filter #(black? fdn-final %) abduce-ns)
                                                                   changes (count-changes fdn fdn-final explained)
                                                                   change-pct (double (* 100.0 (/ changes (count (nodes fdn)))))
                                        ;changes (count-changes fdn fdn-final abduce-ns)
                                        ;change-pct (double (* 100.0 (/ changes (- (count (nodes fdn))
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
                                                                            :Nodes          (count (nodes fdn))
                                                                            :Strokes        (count (strokes fdn))
                                                                            :Microseconds   time-diff
                                                                            :FDNFinal        fdn-final}]
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
                                                         (dissoc :FDNFinal)
                                                         (assoc :ChangedRatioMin ;; (changes+1)/(min+1)
                                                                (double (/ (inc (:Changes results))
                                                                           (inc min-changes)))
                                                                :ExplainedRatioMax
                                                                (double (/ (inc (:Explained results))
                                                                           (inc max-explained)))
                                                                :Same (>= 1 (count (set (map :FDNFinal strat-results)))))))
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
    (is (every? identity (map (fn [fdn] (if (check-structure-axioms-debug fdn)
                                         true (do (visualize fdn) false)))
                              random-graphs)))))
