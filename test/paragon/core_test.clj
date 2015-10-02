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
    (is (= #{:h2 :h3 :j2 :j3 :j4 :s1 :s3 :s4} (set (believed fdn-abduced))))
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
        ;; _ (turn-on-debugging)
        ;; _ (println "****************")
        fdn-abduced (abduce fdn [:E1 :E2 :E3 :E4 :E5 :E6 :E7
                                 :E8 :E9 :E10 :E11 :E12 :E13
                                 :E14 :E16 :E17])
        ;; _ (turn-off-debugging)
        ;; _ (println "****************")
        fdn-contract-e16 (contract fdn-abduced [:E16])
        fdn-contract-e16-e17 (contract fdn-contract-e16 [:E17])
        fdn-contract-i4 (contract fdn-abduced [:I4])
        fdn-contract-i1-i4 (contract fdn-contract-i4 [:I1])]
    (visualize fdn)
    (is (check-structure-axioms fdn-abduced))
    (visualize fdn-abduced)
    (is (check-color-axioms fdn-abduced))
    (is (= #{:E17 :E5 :E10 :E11 :E12 :E13 :E7 :E2 :E3 :E4 :E6 :E8 :E9
             :G2 :G3 :G4 :G6 :G7 :G8 :I8 :I2 :I4a :I6 :I4}
           (set (believed fdn-abduced))))
    #_(visualize fdn-contract-e16)
    (is (check-structure-axioms fdn-contract-e16))
    (is (check-color-axioms fdn-contract-e16))    
    (is (check-color-axioms fdn-contract-e16-e17))
    (is (not (black? fdn-contract-e16 :E16)))
    (is (not (black? fdn-contract-e16-e17 :E17)))
    (is (not (black? fdn-contract-i4 :I4)))
    (is (not (black? fdn-contract-i1-i4 :I1)))))

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

(def test-priority-fdn
  (-> (new-fdn)
      (add-initial :t :x :y)
      (can-explain [:t] [:w :z])
      (can-explain [:w] [:v])
      (can-explain [:x :y] [:z])
      (can-explain [:z] [:p])))

(deftest test-priority-z
  (let [fdn-z (abduce test-priority-fdn [:z])]
    #_(visualize fdn-z)
    (is (= #{:z :p :t :w :v} (set (believed fdn-z))))))

(deftest test-priority-z-negw
  (let [fdn-z (abduce test-priority-fdn [:z])
        fdn-z-negw (with-debugging (contract fdn-z [:w]))]
    #_(visualize fdn-z-negw)
    (is (= #{:z :p :x :y} (set (believed fdn-z-negw))))))

(deftest test-priority-z-negw-negp
  (let [fdn-z (abduce test-priority-fdn [:z])
        fdn-z-negw (contract fdn-z [:w])
        fdn-z-negw-negp (with-debugging (contract fdn-z-negw [:p]))]
    #_(visualize fdn-z-negw-negp)
    ;; leaving y behind is not desirable; but maybe epistemically appropriate?
    (is (= #{:y} (set (believed fdn-z-negw-negp))))))

(deftest test-priority-z-negw-w
  (let [fdn-z (abduce test-priority-fdn [:z])
        fdn-z-negw (contract fdn-z [:w])
        fdn-z-negw-w (with-debugging (abduce fdn-z-negw [:w]))]
    #_(visualize fdn-z-negw-w)
    (is (= #{:z :p :t :w :v :x :y} (set (believed fdn-z-negw-w))))))

(deftest test-priority-z-negw-negx
  (let [fdn-z (abduce test-priority-fdn [:z])
        fdn-z-negw (contract fdn-z [:w])
        fdn-z-negw-negx (with-debugging (contract fdn-z-negw [:x]))]
    #_(visualize fdn-z-negw-negx)
    ;; leaving y behind is not desirable; but maybe epistemically appropriate?
    (is (= #{:y} (set (believed fdn-z-negw-negx))))))

(deftest test-priority-z-negw-negx-w
  (let [fdn-z (abduce test-priority-fdn [:z])
        fdn-z-negw (contract fdn-z [:w])
        fdn-z-negw-negx (contract fdn-z-negw [:x])
        fdn-z-negw-negx-w (with-debugging (abduce fdn-z-negw-negx [:w]))]
    #_(visualize fdn-z-negw-negx-w)
    ;; leaving y behind is not desirable; but maybe epistemically appropriate?
    (is (= #{:z :p :t :w :v :y} (set (believed fdn-z-negw-negx-w))))))

(deftest test-priority-z-negw-negx-w-negp
  (let [fdn-z (abduce test-priority-fdn [:z])
        fdn-z-negw (contract fdn-z [:w])
        fdn-z-negw-negx (contract fdn-z-negw [:x])
        fdn-z-negw-negx-w (abduce fdn-z-negw-negx [:w])
        fdn-z-negw-negx-w-negp (with-debugging (contract fdn-z-negw-negx-w [:p]))]
    #_(visualize fdn-z-negw-negx-w-negp)
    ;; leaving y behind is not desirable; but maybe epistemically appropriate?
    (is (= #{:y} (set (believed fdn-z-negw-negx-w-negp))))))

(deftest test-priority-xy
  (let [fdn-xy (with-debugging (abduce test-priority-fdn [:x :y]))]
    #_(visualize fdn-xy)
    (is (= #{:x :y :z :p} (set (believed fdn-xy))))))

(deftest test-priority-xy-negxy
  (let [fdn-xy (abduce test-priority-fdn [:x :y])
        fdn-xy-negxy (with-debugging (contract fdn-xy [:x :y]))]
    #_(visualize fdn-xy-negxy)
    (is (= #{} (set (believed fdn-xy-negxy))))))

(deftest test-priority-xy-p
  (let [fdn-xy (abduce test-priority-fdn [:x :y])
        fdn-xy-p (with-debugging (abduce fdn-xy [:p]))]
    #_(visualize fdn-xy-p)
    (is (= #{:x :y :z :p} (set (believed fdn-xy-p))))))

(deftest test-priority-xy-p-negxy
  (let [fdn-xy (abduce test-priority-fdn [:x :y])
        fdn-xy-p (abduce fdn-xy [:p])
        fdn-xy-p-negxy (with-debugging (contract fdn-xy-p [:x :y]))]
    #_(visualize fdn-xy-p-negxy)
    (is (= #{:p :z :t :w :v} (set (believed fdn-xy-p-negxy))))))

(deftest test-priority-t
  (let [fdn-t (with-debugging (abduce test-priority-fdn [:t]))]
    #_(visualize fdn-t)
    (is (= #{:t :w :v :z :p} (set (believed fdn-t))))))

(deftest test-priority-t-negt
  (let [fdn-t (abduce test-priority-fdn [:t])
        fdn-t-negt (with-debugging (contract fdn-t [:t]))]
    #_(visualize fdn-t-negt)
    (is (= #{} (set (believed fdn-t-negt))))))

(deftest test-priority-t-p
  (let [fdn-t (abduce test-priority-fdn [:t])
        fdn-t-p (with-debugging (abduce fdn-t [:p]))]
    #_(visualize fdn-t-p)
    (is (= #{:t :w :v :z :p} (set (believed fdn-t-p))))))

(deftest test-priority-t-p-negt
  (let [fdn-t (abduce test-priority-fdn [:t])
        fdn-t-p (abduce fdn-t [:p])
        fdn-t-p-negt (with-debugging (contract fdn-t-p [:t]))]
    #_(visualize fdn-t-p-negt)
    (is (= #{:x :y :z :p} (set (believed fdn-t-p-negt))))))

(def test-skidding-fdn
  (-> (new-fdn)
      (add-initial :drunk)
      (add-initial :speeding)
      (can-explain [:drunk] [:pulled-brake])
      (can-explain [:pulled-brake] [:locking :pulled-position :testimony])
      (can-explain [:speeding] [:mark-nature :control-loss])
      (can-explain [:control-loss] [:skidding])
      (can-explain [:locking] [:skidding])
      (can-explain [:skidding] [:tire-marks :crash])))

(deftest test-skidding-crash
  (let [fdn-crash (with-debugging (abduce test-skidding-fdn [:crash]))]
    #_(visualize fdn-crash)
    (is (= #{:speeding :mark-nature :control-loss :skidding :tire-marks :crash} (set (believed fdn-crash))))))

(deftest test-skidding-crash-negspeeding
  (let [fdn-crash (abduce test-skidding-fdn [:crash])
        fdn-crash-negspeeding (with-debugging (contract fdn-crash [:speeding]))]
    #_(visualize fdn-crash-negspeeding)
    (is (= #{:drunk :pulled-brake :testimony :pulled-position :locking :skidding :tire-marks :crash}
           (set (believed fdn-crash-negspeeding))))))

(def test-grasswet-fdn
  (-> (new-fdn)
      (add-initial :rain)
      (add-initial :sprinkler)
      (can-explain [:rain] [:grass-wet])
      (can-explain [:sprinkler] [:grass-wet])))

(deftest test-grasswet-grasswet
  (let [fdn-grasswet (with-debugging (abduce test-grasswet-fdn [:grass-wet]))]
    #_(visualize fdn-grasswet)
    (is (= #{:grass-wet :rain} (set (believed fdn-grasswet))))))

(deftest test-grasswet-grasswet-negrain
  (let [fdn-grasswet (abduce test-grasswet-fdn [:grass-wet])
        fdn-grasswet-negrain (with-debugging (contract fdn-grasswet [:rain]))]
    #_(visualize fdn-grasswet-negrain)
    (is (= #{:grass-wet :sprinkler} (set (believed fdn-grasswet-negrain))))))

(deftest test-grasswet-grasswet-negrain-negsprinkler
  (let [fdn-grasswet (abduce test-grasswet-fdn [:grass-wet])
        fdn-grasswet-negrain (contract fdn-grasswet [:rain])
        fdn-grasswet-negrain-negsprinkler (with-debugging (contract fdn-grasswet-negrain [:sprinkler]))]
    #_(visualize fdn-grasswet-negrain-negsprinkler)
    (is (= #{} (set (believed fdn-grasswet-negrain-negsprinkler))))))

(deftest test-grasswet-grasswet-negrain-negsprinkler-grasswet
  (let [fdn-grasswet (abduce test-grasswet-fdn [:grass-wet])
        fdn-grasswet-negrain (contract fdn-grasswet [:rain])
        fdn-grasswet-negrain-negsprinkler (contract fdn-grasswet-negrain [:sprinkler])
        fdn-grasswet-negrain-negsprinkler-grasswet (with-debugging (abduce fdn-grasswet-negrain-negsprinkler [:grass-wet]))]
    #_(visualize fdn-grasswet-negrain-negsprinkler-grasswet)
    (is (= #{:grass-wet :rain} (set (believed fdn-grasswet-negrain-negsprinkler-grasswet))))))

(deftest test-grasswet-grasswet-negrain-negsprinkler-negrain
  (let [fdn-grasswet (abduce test-grasswet-fdn [:grass-wet])
        fdn-grasswet-negrain (contract fdn-grasswet [:rain])
        fdn-grasswet-negrain-negsprinkler (contract fdn-grasswet-negrain [:sprinkler])
        fdn-grasswet-negrain-negsprinkler-negrain (with-debugging (contract fdn-grasswet-negrain-negsprinkler [:rain]))]
    #_(visualize fdn-grasswet-negrain-negsprinkler-negrain)
    (is (= #{} (set (believed fdn-grasswet-negrain-negsprinkler-negrain))))))

(deftest test-grasswet-grasswet-negrain-negsprinkler-negrain-grasswet
  (let [fdn-grasswet (abduce test-grasswet-fdn [:grass-wet])
        fdn-grasswet-negrain (contract fdn-grasswet [:rain])
        fdn-grasswet-negrain-negsprinkler (contract fdn-grasswet-negrain [:sprinkler])
        fdn-grasswet-negrain-negsprinkler-negrain (contract fdn-grasswet-negrain-negsprinkler [:rain])
        fdn-grasswet-negrain-negsprinkler-negrain-grasswet (with-debugging (abduce fdn-grasswet-negrain-negsprinkler-negrain [:grass-wet]))]
    #_(visualize fdn-grasswet-negrain-negsprinkler-negrain-grasswet)
    ;; this case is not handled well; see notes about "cases not supported"
    (is (= #{:grass-wet :rain} (set (believed fdn-grasswet-negrain-negsprinkler-negrain-grasswet))))))

(def test-priority-inconsistency-fdn
  (-> (new-fdn)
      (add-initial :t :x :y)
      (can-explain [:t] [:w :z])
      (can-explain [:w] [:v])
      (can-explain [:x :y] [:z])
      (can-explain [:z] [:p])
      (add-inconsistencies [:t :x])))

(deftest test-priority-inconsistency-z
  (let [fdn-z (with-debugging (abduce test-priority-inconsistency-fdn [:z]))]
    #_(visualize fdn-z)
    (is (= #{:z :p :t :w :v} (set (believed fdn-z))))))

(deftest test-priority-inconsistency-z-negw
  (let [fdn-z (abduce test-priority-inconsistency-fdn [:z])
        fdn-z-negw (with-debugging (contract fdn-z [:w]))]
    #_(visualize fdn-z-negw)
    (is (= #{:z :p :x :y} (set (believed fdn-z-negw))))))

(deftest test-priority-inconsistency-z-negw-t
  (let [fdn-z (abduce test-priority-inconsistency-fdn [:z])
        fdn-z-negw (contract fdn-z [:w])
        fdn-z-negw-t (with-debugging (abduce fdn-z-negw [:t]))]
    #_(visualize fdn-z-negw-t)
    (is (= #{:z :p :t :w :v :y} (set (believed fdn-z-negw-t))))))

(deftest test-priority-inconsistency-z-negw-t-negz
  (let [fdn-z (abduce test-priority-inconsistency-fdn [:z])
        fdn-z-negw (contract fdn-z [:w])
        fdn-z-negw-t (abduce fdn-z-negw [:t])
        fdn-z-negw-t-negz (with-debugging (contract fdn-z-negw-t [:z]))]
    #_(visualize fdn-z-negw-t-negz)
    (is (= #{:y} (set (believed fdn-z-negw-t-negz))))))

(deftest test-priority-inconsistency-z-negw-t-negz-p
  (let [fdn-z (abduce test-priority-inconsistency-fdn [:z])
        fdn-z-negw (contract fdn-z [:w])
        fdn-z-negw-t (abduce fdn-z-negw [:t])
        fdn-z-negw-t-negz (contract fdn-z-negw-t [:z])
        fdn-z-negw-t-negz-p (with-debugging (abduce fdn-z-negw-t-negz [:p]))]
    #_(visualize fdn-z-negw-t-negz-p)
    (is (= #{:p :z :x :y} (set (believed fdn-z-negw-t-negz-p))))))

(deftest test-priority-inconsistency-z-negw-t-negz-p-negy
  (let [fdn-z (abduce test-priority-inconsistency-fdn [:z])
        fdn-z-negw (contract fdn-z [:w])
        fdn-z-negw-t (abduce fdn-z-negw [:t])
        fdn-z-negw-t-negz (contract fdn-z-negw-t [:z])
        fdn-z-negw-t-negz-p (abduce fdn-z-negw-t-negz [:p])
        fdn-z-negw-t-negz-p-negy (with-debugging (contract fdn-z-negw-t-negz-p [:y]))]
    #_(visualize fdn-z-negw-t-negz-p-negy)
    (is (= #{:z :p :v :w :t} (set (believed fdn-z-negw-t-negz-p-negy))))))
