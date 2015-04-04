(ns paragon.core-test
  (:require [clojure.test :refer :all]
            [paragon.core :refer :all])
  (:require [taoensso.timbre.profiling :refer (profile)]))

(deftest test-expand-explains
  #_(turn-on-debugging)
  (let [jg (-> (new-just-graph)
               (can-explain [:h1] [:s1])
               (can-explain [:h1] [:s2])
               (can-explain [:h2] [:s1])
               (can-explain [:h2] [:s4])
               (can-explain [:h3] [:s3])
               (can-explain [:h3] [:s4])
               (can-explain [:j1 :j2] [:h1])
               (can-explain [:j2 :j3 :j4] [:h3])
               (premise :j1 :j2 :j3 :j4 :h2)
               (add-inconsistencies [:h1 :h2 :h3]))
        jg-abduced (abduce jg [:s1 :s2 :s3 :s4])]
    #_(visualize jg)
    #_(visualize jg-abduced)
    #_(save-pdf jg-expanded "test.pdf")
    (is (= #{:h1 :h2 :j1 :j2 :s1 :s2 :s4} (set (believed jg-abduced))))))

(deftest test-peyer
  #_(turn-on-debugging)
  (let [jg (-> (new-just-graph)
               (premise :I1 :G1 :G6 :G4 :G5 :I2 :G3 :I3 :G1 :I4 :I4a :G2 :I5
                        :I6 :G7 :I7 :G8 :I8)
               (can-explain [:I1] [:E1])
               (can-explain [:G1] [:E1])
               (can-explain [:G6] [:E2])
               (can-explain [:G4] [:E3])
               (can-explain [:G5] [:E4])
               (can-explain [:I2] [:E4])
               (can-explain [:I2] [:E5])
               (can-explain [:G3] [:E6])
               (can-explain [:I3] [:E6])
               (can-explain [:G1] [:E7])
               (can-explain [:I4] [:E7])
               (can-explain [:I4a] [:E8])
               (can-explain [:G2] [:E9])
               (can-explain [:I5] [:E9])
               (can-explain [:G1] [:E10])
               (can-explain [:I6] [:E10])
               (can-explain [:I6] [:E11])
               (can-explain [:G7] [:E12])
               (can-explain [:I7] [:E12])
               (can-explain [:G8] [:E13])
               (can-explain [:I7] [:E13])
               (can-explain [:G1] [:E14])
               (can-explain [:I1] [:E14])
               (can-explain [:I1] [:E16])
               (can-explain [:I8] [:E17])
               (add-inconsistencies [:G1 :I1] [:G1 :I8] [:I1 :I8]
                                    [:G2 :I5] [:G3 :I3] [:G5 :I2] [:G7 :I7]))
        jg-expanded (abduce jg [:E1 :E2 :E3 :E4 :E5 :E6 :E7
                                :E8 :E9 :E10 :E11 :E12 :E13
                                :E14 :E15 :E16 :E17])
        jg-contract-e16 (contract jg-expanded [:E16])
        jg-contract-e17-e16 (contract jg-contract-e16 [:E17])
        jg-contract-i4 (contract jg-expanded [:I4])
        jg-contract-i1-i4 (contract jg-contract-i4 [:I1])]
    (is (check-structure-axioms jg-expanded))
    (is (check-color-axioms jg-expanded))
    (is (= #{:E10 :E11 :E12 :E13 :E17 :E2 :E3 :E4
             :E5 :E6 :E7 :E8 :E9 :G4 :G6 :G8 :I2
             :I3 :I4 :I4a :I5 :I6 :I7 :I8}
           (set (believed jg-expanded))))
    (is (check-structure-axioms jg-contract-e16))
    (is (check-color-axioms jg-contract-e16))
    (is (check-color-axioms jg-contract-e17-e16))
    (is (not ((set (believed jg-contract-e16)) :E16)))
    (is (not ((set (believed jg-contract-e17-e16)) :E17)))
    (is (not ((set (believed jg-contract-i4)) :I4)))
    (is (not ((set (believed jg-contract-i1-i4)) :I1)))))

(deftest test-random
  (let [premise-count 500
        premise-stroke-cardinality 100
        stroke-count 200
        expand-count 50
        jg (apply premise (new-just-graph) (range premise-count))
        jg2 (reduce (fn [jg s] (forall-just jg (take (rand-int premise-stroke-cardinality)
                                                     (shuffle (range premise-count)))
                                            s))
                    jg (range premise-count (+ premise-count stroke-count)))
        jg3 (reduce (fn [jg [s n]] (exists-just jg [s] n))
                    jg2 (map (fn [s n] [s n])
                             (range premise-count (+ premise-count stroke-count))
                             (range (+ premise-count stroke-count)
                                    (+ premise-count stroke-count stroke-count))))]
    (is (check-structure-axioms jg3))
    (is (check-color-axioms jg3))
    (profile :debug :check-structure-axioms (check-structure-axioms jg3))
    (profile :debug :check-color-axioms (check-color-axioms jg3))
    (profile :debug :expand (expand jg3 (take expand-count (shuffle (concat (nodes jg3) (strokes jg3))))))))