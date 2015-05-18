(ns paragon.core-test
  (:require [clojure.test :refer :all]
            [paragon.core :refer :all]
            [loom.graph :as graph]
            [loom.alg :as alg]
            [clojure.set :as set])
  (:require [taoensso.timbre.profiling :refer (profile)]))

(deftest test-basic-operations
  (let [jg (-> (new-just-graph)
               (add-initial :n))]
    (is (initial? jg :n))))

(deftest test-convert-to-prolog
  (let [jg (-> (new-just-graph)
               (add-initial :n))
        jg2 (-> (new-just-graph)
                (add-initial :p)
                (add-initial :q)
                (forall-just [:p :q] :s)
                (exists-just [:s] :r))
        jg3 (-> (new-just-graph)
                (add-initial :p)
                (add-initial :q)
                (forall-just [:p] :s1)
                (forall-just [:q] :s2)
                (exists-just [:s1 :s2] :r))
        jg4 (-> (new-just-graph)
                (add-initial :p)
                (add-initial :q)
                (forall-just [:p] :s1)
                (forall-just [:q] :s2)
                (exists-just [:s1 :s2] :r)
                (add-inconsistencies [:p :q]))
        jg5 (-> (new-just-graph)
                (add-initial :p)
                (add-initial :q)
                (forall-just [:p] :s1)
                (forall-just [:q] :s2)
                (exists-just [:s1 :s2] :r)
                (add-inconsistencies [:p :q])
                (assert-black :p))]
    (is (= "" (convert-to-prolog jg)))
    (is (= "r :- q, p." (convert-to-prolog jg2)))
    (is (= "r :- p.\nr :- q." (convert-to-prolog jg3)))
    (is (= "p :- not(q).\nq :- not(p).\nr :- p.\nr :- q." (convert-to-prolog jg4)))
    (is (= "p :- not(q).\np.\nq :- not(p).\nr :- p.\nr :- q." (convert-to-prolog jg5)))))

(deftest test-expand-explains
  (let [jg (-> (new-just-graph)
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
        jg-abduced (abduce jg [:s1 :s2 :s3 :s4])]
    #_(visualize jg)
    #_(visualize jg-abduced)
    #_(save-pdf jg-expanded "test.pdf")
    (is (= #{:h1 :h2 :j1 :j2 :j3 :s1 :s2 :s4} (set (believed jg-abduced))))
    #_(is (= "h1 :- j2, j1.\nh1 :- not(h2).\nh1 :- not(h3).\nh2 :- not(h1).\nh2 :- not(h3).\nh3 :- j4, j3, j2.\nh3 :- not(h1).\nh3 :- not(h2).\ns1 :- h1.\ns1 :- h2.\ns2 :- h1.\ns3 :- h3.\ns4 :- h2.\ns4 :- h3." (convert-to-prolog jg)))))

(deftest test-convert-to-prolog
  (let [jg (-> (new-just-graph)
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
        jg-abduced (abduce jg [:s1 :s2 :s3 :s4])]
    #_(visualize jg-abduced)
    #_(println (convert-to-prolog jg-abduced))))

(deftest test-peyer
  (let [jg (-> (new-just-graph)
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
        jg-abduced (abduce jg [:E1 :E2 :E3 :E4 :E5 :E6 :E7
                                :E8 :E9 :E10 :E11 :E12 :E13
                                :E14 :E15 :E16 :E17])
        jg-contract-e16 (contract jg-abduced [:E16])
        jg-contract-e17-e16 (contract jg-contract-e16 [:E17])
        jg-contract-i4 (contract jg-abduced [:I4])
        jg-contract-i1-i4 (contract jg-contract-i4 [:I1])]
    (is (check-structure-axioms jg-abduced))
    (is (check-color-axioms jg-abduced))
    (is (= #{:E10 :E11 :E12 :E13 :E1 :E14 :E7 :E2 :E3 :E4 :E6 :E8 :E9
             :G1 :G5 :G2 :G3 :G4 :G6 :G7 :G8 :I4a :I6}
           (set (believed jg-abduced))))
    #_(visualize jg-abduced)
    (is (check-structure-axioms jg-contract-e16))
    (is (check-color-axioms jg-contract-e16))
    (is (check-color-axioms jg-contract-e17-e16))
    (is (not ((set (believed jg-contract-e16)) :E16)))
    (is (not ((set (believed jg-contract-e17-e16)) :E17)))
    (is (not ((set (believed jg-contract-i4)) :I4)))
    (is (not ((set (believed jg-contract-i1-i4)) :I1)))))

(def g-transpose
  (memoize (fn [g] (graph/transpose g))))

(def get-ancestors
  (memoize (fn [g n]
             (let [gt (g-transpose g)]
               (alg/post-traverse gt n)))))

(defn strategy-pref-ancestors
  [jg ns-or-ss min?]
  (let [ns (set (filter #(node? jg %) ns-or-ss))
        n-ancestors (into {} (for [n ns] [n (set (filter #(node? jg %) (get-ancestors (:graph jg) n)))]))
        ns-sorted (sort-by #(count (set/intersection ns (get n-ancestors %))) ns)]
    #_(prn n-ancestors)
    #_(prn (map (fn [n] [n (count (set/intersection ns (get n-ancestors n)))]) ns))
    (if min? (first ns-sorted) (last ns-sorted))))

(deftest test-contraction-1
    (let [jg (-> (new-just-graph)
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
          jg-black (-> jg
                       (abduce [:c :d :e :f :a :g :h :b])
                       (assert-black [".g"]))
          jg-contracted (contract jg-black [:a :b :e] :white-strategy #(strategy-pref-ancestors %1 %2 true))]
      (assert (check-structure-axioms jg))
      #_(save-pdf jg-contracted "ex-fdn.pdf")
      #_(visualize jg-contracted)))

(deftest test-contraction-2
    (let [jg (-> (new-just-graph)
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
          jg-black (-> jg
                       (abduce [:b :c :d :e :f :a :g])
                       (expand [".g"]))
          jg-contracted (contract jg-black [:a] :white-strategy #(strategy-pref-ancestors %1 %2 true))]
      #_(println (convert-to-com-input jg [:a]))
      #_(visualize (process-with-com jg [:a] true))
      #_(visualize (process-with-com jg [:a] false))
      #_(save-pdf jg-contracted "ex-fdn.pdf")
      #_(visualize jg-contracted)))

(deftest test-contraction-sprig-top
    (let [jg (-> (new-just-graph)
                 (add-initial :a :b :c :d)
                 (forall-just [:a :b] :ab)
                 (forall-just [:c :d] :cd)
                 (exists-just [:ab] :e)
                 (exists-just [:cd] :f)
                 (forall-just [:e :f] :ef)
                 (exists-just [:ef] :g))
          jg-black (-> jg
                       (abduce [:a :b :c :d])
                       (expand [:g]))
          jg-contracted (contract jg-black [:b] :white-strategy #(strategy-pref-ancestors %1 %2 true))]
      #_(visualize (process-with-com jg [:b]))
      #_(save-pdf jg-contracted "ex-fdn.pdf")
      #_(visualize jg-contracted)))

(deftest test-inconsistency-1
  (let [jg (-> (new-just-graph)
               (add-initial :c :b :a)
               (forall-just [:a] :sa)
               (exists-just [:scb] :e)
               (forall-just [:c :b] :scb)
               (exists-just [:sa] :e)
               (add-inconsistencies [:b :a]))
        jg2 (abduce jg [:a])
        jg3 (abduce jg [:b])
        jg4 (abduce jg [:c])
        jg5 (abduce jg [:c :a])
        jg6 (abduce jg [:c :b])]
    #_(save-pdf jg "ex-inconsistency-1.pdf")
    #_(save-pdf jg2 "ex-inconsistency-2.pdf")
    #_(save-pdf jg3 "ex-inconsistency-3.pdf")
    #_(save-pdf jg4 "ex-inconsistency-4.pdf")
    #_(save-pdf jg5 "ex-inconsistency-5.pdf")
    #_(save-pdf jg6 "ex-inconsistency-6.pdf")
    #_(visualize jg)
    #_(visualize jg2)
    #_(visualize jg3)
    #_(visualize jg4)
    #_(visualize jg5)
    #_(visualize jg6)))

(deftest test-random
  (let [premise-count 500
        premise-stroke-cardinality 100
        stroke-count 200
        expand-count 50
        jg (apply add-initial (new-just-graph) (range premise-count))
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
