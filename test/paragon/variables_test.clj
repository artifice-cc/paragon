(ns paragon.variables-test
  (:require [clojure.test :refer :all]
            [paragon.core :refer :all]
            [paragon.axioms :refer :all]
            [paragon.coloring :refer :all]
            [paragon.visualization :refer :all]
            [paragon.interfaces :refer :all]
            [paragon.builders :refer :all]
            [paragon.strategies :refer :all]))

(deftest test-variables
  (turn-off-debugging)
  (turn-off-stroke-labels)
  (turn-off-priority-labels)
  (let [fdn-father (-> (new-fdn)
                       (candidates [:parent :x :y] [{:x :joe :y :jane} {:x :jim :y :sam}])
                       (candidates [:male :x] [{:x :joe} {:x :jim}])
                       (can-explain [[:parent :x :y] [:male :x]] [[:father :x :y]]))
        fdn-father-abduced (abduce fdn-father [[:father :x :y]])
        fdn-father-abduced-x-jim-contracted (contract fdn-father-abduced [[= :x :jim]])]
    (is (= #{[:parent :x :y] [:male :x] [:father :x :y]} (set (predicates fdn-father))))
    (is (= #{:x :y} (set (variables fdn-father))))
    (is (= #{[:parent :jim :sam] [:father :jim :sam] [:male :jim]}
           (set (believed-predicate-assignments fdn-father-abduced))))
    (is (= #{[:parent :joe :jane] [:father :joe :jane] [:male :joe]}
           (set (believed-predicate-assignments fdn-father-abduced-x-jim-contracted))))
    #_(visualize fdn-father-abduced)
    #_(visualize fdn-father-abduced-x-jim-contracted)))


