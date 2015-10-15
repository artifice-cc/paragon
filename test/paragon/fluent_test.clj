(ns paragon.fluent-test
  (:require [clojure.test :refer :all]
            [paragon.core :refer :all]
            [paragon.axioms :refer :all]
            [paragon.coloring :refer :all]
            [paragon.visualization :refer :all]
            [paragon.interfaces :refer :all]
            [paragon.builders :refer :all]
            [paragon.strategies :refer :all]))

(deftest test-grounded-fluents-agree
  (is (grounded-fluents-agree? {:x 1 :y 2} {:x 1 :y 2}))
  (is (grounded-fluents-agree? {:x 1 :y 2} {:x 1 :y 2 :z 3}))
  (is (grounded-fluents-agree? {:x 1 :y 2 :z 3} {:x 1 :y 2}))
  (is (grounded-fluents-agree? {} {:x 1 :y 2}))
  (is (grounded-fluents-agree? {:x 1 :y 2 :z 3} {}))
  (is (grounded-fluents-agree? {:x 1} {:y 2}))
  (is (not (grounded-fluents-agree? {:x 1 :y 3 :z 3} {:x 1 :y 2})))
  (is (not (grounded-fluents-agree? {:x 1 :y 2} {:x 1 :y 3})))
  (is (not (grounded-fluents-agree? {:x 1 :y 2 :z 4} {:x 1 :y 3 :z 4}))))

(deftest test-fluents-1
  (let [fdn (-> (new-fdn)
                (add-initial :p)
                (set-fluents ".p" :x)
                (set-grounded-fluents {:x 2}))]
    #_(visualize fdn)
    (is (= [:x] (fdnfluents fdn ".p")))
    (is (= {:x 2} (fdn-grounded-fluents fdn ".p")))))

(deftest test-fluents-2
  (let [fdn (-> (new-fdn)
                (add-initial :p)
                (set-fluents ".p" :x :y)
                (set-grounded-fluents {:x 2})
                (set-grounded-fluents {:y 3}))]
    #_(visualize fdn)
    (is (= [:x :y] (fdnfluents fdn ".p")))
    (is (= {:x 2 :y 3} (fdn-grounded-fluents fdn ".p")))))

(deftest test-fluents-3
  (let [fdn (-> (new-fdn)
                (add-initial :p)
                (add-initial :q)
                (can-explain [:p :q] [:r])
                (set-fluents ".p" :x)
                (set-fluents ".q" :y)
                (set-grounded-fluents {:x 2})
                (set-grounded-fluents {:y 3}))]
    #_(visualize fdn)
    (is (= [:x] (fdnfluents fdn :p)))
    (is (= [:y] (fdnfluents fdn :q)))
    (is (= {:x 2} (fdn-grounded-fluents fdn :p)))
    (is (= {:y 3} (fdn-grounded-fluents fdn :q)))
    (is (= [:x :y] (fdnfluents fdn :r)))
    (is (= [:x :y] (fdnfluents fdn "p&q->r")))
    (is (= {:x 2 :y 3} (fdn-grounded-fluents fdn "p&q->r")))
    (is (= {:x 2 :y 3} (fdn-grounded-fluents fdn :r)))
    (is (= {:x 2 :y 3} (fdn-grounded-fluents fdn "p&q->r")))))

(deftest test-fluents-4
  (let [fdn (-> (new-fdn)
                (add-initial :p)
                (add-initial :q)
                (can-explain [:p] [:r])
                (can-explain [:q] [:r])
                (set-fluents ".p" :x)
                (set-fluents ".q" :y)
                (set-grounded-fluents {:x 2})
                (set-grounded-fluents {:y 3}))]
    #_(visualize fdn)
    (is (= [:x] (fdnfluents fdn :p)))
    (is (= [:y] (fdnfluents fdn :q)))
    (is (= {:x 2} (fdn-grounded-fluents fdn :p)))
    (is (= {:y 3} (fdn-grounded-fluents fdn :q)))
    (is (= [:x :y] (fdnfluents fdn :r)))
    (is (= [:x :y] (fdnfluents fdn "p&q->r")))
    (is (= {:x 2 :y 3} (fdn-grounded-fluents fdn "p&q->r")))
    (is (= {:x 2 :y 3} (fdn-grounded-fluents fdn :r)))
    (is (= {:x 2 :y 3} (fdn-grounded-fluents fdn "p&q->r")))))

(deftest test-fluents-4
  (let [fdn (-> (new-fdn)
                (add-initial :pos)
                (add-initial :neg)
                (can-explain [:pos] [:r] "x > 0" (fn [{:keys [x]}] (> x 0)))
                (can-explain [:neg] [:r] "x < 0" (fn [{:keys [x]}] (< x 0)))
                (set-fluents ".pos" :x)
                (set-fluents ".neg" :x)
                (set-grounded-fluents {:x 2}))]
    (visualize fdn)
))

(comment
  (deftest test-fluents-6
    (let [fdn (-> (new-fdn)
                  (add-initial :p)
                  (add-initial :q)
                  (can-explain [:p :q] [:r])
                  (set-fluents :p :x)
                  (set-fluents :q :y)
                  (set-grounded-fluents :p {:x 2})
                  (set-grounded-fluents :q {:y 3})
                  (set-grounded-fluents "p&q->r" {:y 5}))]
      #_(visualize fdn)
      (is (= [:x] (fdnfluents fdn :p)))
      (is (= [:y] (fdnfluents fdn :q)))
      (is (= {:x 2} (fdn-grounded-fluents fdn :p)))
      (is (= {:y 3} (fdn-grounded-fluents fdn :q)))
      (is (= [:x :y] (fdnfluents fdn :r)))
      (is (= [:x :y] (fdnfluents fdn "p&q->r")))
      (is (= {:y 5} (fdn-grounded-fluents fdn "p&q->r")))
      (is (= [] (fdnin fdn "p&q->r")))
      (is (= [] (fdnout fdn :p)))
      (is (= [] (fdnout fdn :q))))))
