(ns paragon.core-test
  (:require [clojure.test :refer :all]
            [paragon.core :refer :all]
            [paragon.axioms :refer :all]
            [paragon.coloring :refer :all]
            [paragon.visualization :refer :all]
            [paragon.interfaces :refer :all]
            [paragon.builders :refer :all]
            [paragon.strategies :refer :all]))

(deftest test-basic-operations
  (let [fdn (-> (new-fdn)
               (add-initial :n))]
    (is (initial? fdn :n))))

(deftest test-convert-to-prolog
  (let [fdn (-> (new-fdn)
               (add-initial :n))
        fdn2 (-> (new-fdn)
                (add-initial :p)
                (add-initial :q)
                (forall-just [:p :q] :s)
                (exists-just [:s] :r))
        fdn3 (-> (new-fdn)
                (add-initial :p)
                (add-initial :q)
                (forall-just [:p] :s1)
                (forall-just [:q] :s2)
                (exists-just [:s1 :s2] :r))
        fdn4 (-> (new-fdn)
                (add-initial :p)
                (add-initial :q)
                (forall-just [:p] :s1)
                (forall-just [:q] :s2)
                (exists-just [:s1 :s2] :r)
                (add-inconsistencies [:p :q]))
        fdn5 (-> (new-fdn)
                (add-initial :p)
                (add-initial :q)
                (forall-just [:p] :s1)
                (forall-just [:q] :s2)
                (exists-just [:s1 :s2] :r)
                (add-inconsistencies [:p :q])
                (assert-black :p))]
    (is (= "" (convert-to-prolog fdn)))
    (is (= "r :- q, p." (convert-to-prolog fdn2)))
    (is (= "r :- p.\nr :- q." (convert-to-prolog fdn3)))
    (is (= "p :- not(q).\nq :- not(p).\nr :- p.\nr :- q." (convert-to-prolog fdn4)))
    (is (= "p :- not(q).\np.\nq :- not(p).\nr :- p.\nr :- q." (convert-to-prolog fdn5)))))

(deftest test-expand-explains
  (let [fdn (-> (new-fdn)
               (can-explain [:h1] [:s1])
               (can-explain [:h1] [:s2])
               (can-explain [:h2] [:s1])
               (can-explain [:h2] [:s4])
               (can-explain [:h3] [:s3])
               (can-explain [:h3] [:s4])
               (can-explain [:j1 :j2] [:h1])
               (can-explain [:j2 :j3 :j4] [:h3])
               (add-initial :j1 :j2 :j3 :j4 :h2)
               (add-inconsistencies [:h1 :h2 :h3]))
        fdn-abduced (abduce fdn [:s1 :s2 :s3 :s4])]
    (is (= #{:h1 :h2 :j1 :j2 :j3 :s1 :s2 :s4} (set (believed fdn-abduced))))
    #_(is (= "h1 :- j2, j1.\nh1 :- not(h2).\nh1 :- not(h3).\nh2 :- not(h1).\nh2 :- not(h3).\nh3 :- j4, j3, j2.\nh3 :- not(h1).\nh3 :- not(h2).\ns1 :- h1.\ns1 :- h2.\ns2 :- h1.\ns3 :- h3.\ns4 :- h2.\ns4 :- h3." (convert-to-prolog fdn)))))

(deftest test-convert-to-prolog
  (let [fdn (-> (new-fdn)
               (can-explain [:h1] [:s1])
               (can-explain [:h1] [:s2])
               (can-explain [:h2] [:s1])
               (can-explain [:h2] [:s4])
               (can-explain [:h3] [:s3])
               (can-explain [:h3] [:s4])
               (can-explain [:j1 :j2] [:h1])
               (can-explain [:j2 :j3 :j4] [:h3])
               (add-initial :j1 :j2 :j3 :j4 :h2)
               (add-inconsistencies [:h1 :h2 :h3])
               (add-inconsistencies [:h1 :j3]))
        fdn-abduced (abduce fdn [:s1 :s2 :s3 :s4])]
    #_(visualize fdn-abduced)
    #_(println (convert-to-prolog fdn-abduced))))

(deftest test-peyer
  (let [fdn (-> (new-fdn)
               (add-initial :I1 :G1 :G6 :G4 :G5 :I2 :G3 :I3 :G1 :I4 :I4a :G2 :I5
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
        fdn-abduced (abduce fdn [:E1 :E2 :E3 :E4 :E5 :E6 :E7
                                :E8 :E9 :E10 :E11 :E12 :E13
                                :E14 :E16 :E17])
        fdn-contract-e16 (contract fdn-abduced [:E16])
        fdn-contract-e17-e16 (contract fdn-contract-e16 [:E17])
        fdn-contract-i4 (contract fdn-abduced [:I4])
        fdn-contract-i1-i4 (contract fdn-contract-i4 [:I1])]
    (is (check-structure-axioms fdn-abduced))
    (is (check-color-axioms fdn-abduced))
    (is (= #{:E10 :E11 :E12 :E13 :E1 :E14 :E7 :E2 :E3 :E4 :E6 :E8 :E9
             :G1 :G5 :G2 :G3 :G4 :G6 :G7 :G8 :I4a :I6}
           (set (believed fdn-abduced))))
    #_(visualize fdn-abduced)
    (is (check-structure-axioms fdn-contract-e16))
    (is (check-color-axioms fdn-contract-e16))
    (is (check-color-axioms fdn-contract-e17-e16))
    (is (not ((set (believed fdn-contract-e16)) :E16)))
    (is (not ((set (believed fdn-contract-e17-e16)) :E17)))
    (is (not ((set (believed fdn-contract-i4)) :I4)))
    (is (not ((set (believed fdn-contract-i1-i4)) :I1)))))

(deftest test-contraction-1
    (let [fdn (-> (new-fdn)
                 (add-initial :a :b :c :f :d :e :g)
                 (forall-just [:a :b] :ab)
                 (forall-just [:f :d] :fd)
                 (forall-just [:g :i] :gi)
                 (forall-just [:c] :ch)
                 (forall-just [:c :h] :ch2)
                 (forall-just [:e] :eh)
                 (exists-just [:ch] :h)
                 (exists-just [:ab] :i)
                 (exists-just [:eh] :h)
                 (exists-just [:gi :ch2] :j)
                 (exists-just [:fd] :h))
          fdn-black (-> fdn
                       (abduce [:c :d :e :f :a :g :h :b])
                       (assert-black [".g"]))
          fdn-contracted (contract fdn-black [:a :b :e] :white-strategy #(strategy-pref-ancestors %1 %2 true))]
      (assert (check-structure-axioms fdn))
      #_(save-pdf fdn-contracted "ex-fdn.pdf")
      #_(visualize fdn-contracted)))

(deftest test-contraction-2
    (let [fdn (-> (new-fdn)
                 (add-initial :c :d :e :f :a :b :g)
                 (forall-just [:c :d] :cd)
                 (forall-just [:a :b] :ab1)
                 (forall-just [:a :b] :ab2)
                 (forall-just [:g :i] :gi)
                 (forall-just [:f :h] :fh)
                 (forall-just [:e :f] :ef)
                 (exists-just [:cd :ef] :i)
                 (exists-just [:gi :fh] :j)
                 (exists-just [:ab1] :h)
                 (exists-just [:ab2] :g))
          fdn-black (abduce fdn [:b :c :d :e :f :a :g])
          fdn-contracted (contract fdn-black [:a] :white-strategy #(strategy-pref-ancestors %1 %2 true))]
      #_(println (convert-to-com-input fdn [:a]))
      #_(visualize (process-with-com fdn [:a] true))
      #_(visualize (process-with-com fdn [:a] false))
      #_(save-pdf fdn-contracted "ex-fdn.pdf")
      #_(visualize fdn-contracted)))

(deftest test-contraction-sprig-top
    (let [fdn (-> (new-fdn)
                 (add-initial :a :b :c :d)
                 (forall-just [:a :b] :ab)
                 (forall-just [:c :d] :cd)
                 (exists-just [:ab] :e)
                 (exists-just [:cd] :f)
                 (forall-just [:e :f] :ef)
                 (exists-just [:ef] :g))
          fdn-black (abduce fdn [:a :b :c :d :g])
          fdn-contracted (contract fdn-black [:b] :white-strategy #(strategy-pref-ancestors %1 %2 true))]
      #_(visualize (process-with-com fdn [:b]))
      #_(save-pdf fdn-contracted "ex-fdn.pdf")
      #_(visualize fdn-contracted)))

(deftest test-inconsistency-1
  (let [fdn (-> (new-fdn)
               (add-initial :c :b :a)
               (forall-just [:a] :sa)
               (exists-just [:scb] :e)
               (forall-just [:c :b] :scb)
               (exists-just [:sa] :e)
               (add-inconsistencies [:b :a]))
        fdn2 (abduce fdn [:a])
        fdn3 (abduce fdn [:b])
        fdn4 (abduce fdn [:c])
        fdn5 (abduce fdn [:c :a])
        fdn6 (abduce fdn [:c :b])]
    #_(save-pdf fdn "ex-inconsistency-1.pdf")
    #_(save-pdf fdn2 "ex-inconsistency-2.pdf")
    #_(save-pdf fdn3 "ex-inconsistency-3.pdf")
    #_(save-pdf fdn4 "ex-inconsistency-4.pdf")
    #_(save-pdf fdn5 "ex-inconsistency-5.pdf")
    #_(save-pdf fdn6 "ex-inconsistency-6.pdf")
    #_(visualize fdn)
    #_(visualize fdn2)
    #_(visualize fdn3)
    #_(visualize fdn4)
    #_(visualize fdn5)
    #_(visualize fdn6)))

(deftest test-random
  (let [premise-count 500
        premise-stroke-cardinality 100
        stroke-count 200
        expand-count 50
        fdn (apply add-initial (new-fdn) (range premise-count))
        fdn2 (reduce (fn [fdn s] (forall-just fdn (take (rand-int premise-stroke-cardinality)
                                                     (shuffle (range premise-count)))
                                            s))
                    fdn (range premise-count (+ premise-count stroke-count)))
        fdn3 (reduce (fn [fdn [s n]] (exists-just fdn [s] n))
                    fdn2 (map (fn [s n] [s n])
                             (range premise-count (+ premise-count stroke-count))
                             (range (+ premise-count stroke-count)
                                    (+ premise-count stroke-count stroke-count))))]
    (is (check-structure-axioms fdn3))
    (is (check-color-axioms fdn3))))

(deftest test-build-from-query
  (let [fdn-1 (build-from-query :a [:x])
        fdn-2 (build-from-query ["AND" :a :b :c :d] [:x])
        fdn-3 (build-from-query ["OR" :a :b :c :d] [:x])
        fdn-4 (build-from-query ["NOT" :a] [:x])
        fdn-5 (build-from-query ["AND" ["OR" :a :b] :c] [:x])
        fdn-6 (build-from-query ["AND" :c ["OR" :a :b]] [:x])
        fdn-7 (build-from-query ["AND" :c ["OR" :b :a]] [:x])
        fdn-8 (build-from-query ["AND" ["OR" :b :a] :c] [:x])]
    (is (black? (revise fdn-1 [:a]) :x))
    (is (black? (revise fdn-2 [:a :b :c :d]) :x))
    (is (white? (revise fdn-2 [:a :b :c]) :x))
    (is (white? (revise fdn-2 [:a :b]) :x))
    (is (white? (revise fdn-2 [:a]) :x))
    (is (black? (revise fdn-3 [:a :b :c :d]) :x))
    (is (black? (revise fdn-3 [:a :b :c]) :x))
    (is (black? (revise fdn-3 [:a :b]) :x))
    (is (black? (revise fdn-3 [:a]) :x))
    #_(is (white? (revise fdn-4 [:a]) :x))
    #_(visualize fdn-1)
    #_(visualize fdn-2)
    #_(visualize fdn-3)
    #_(visualize fdn-4)
    #_(visualize fdn-5)
    ))

