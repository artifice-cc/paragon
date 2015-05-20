(ns paragon.axioms
  (:require [paragon.core :refer :all])
  (:require [loom.graph :as graph]))

(defn check-axiom-neg1
  "Everything is black or white."
  [jg]
  (every? #{:white :black} (vals (:coloring jg))))

(defn check-axiom-0
  "Nothing is both black and white.

  Axiom 0 is confirmed from the fact that :coloring is a map."
  [jg]
  true)

(defn check-axiom-1
  [jg]
  "Everything is either a node or a stroke."
  (every? #{:node :stroke} (vals (:types jg))))

(defn check-axiom-2
  "Nothing is both a node and a stroke.

  Axiom 2 is confirmed from the fact that :types is a map."
  [jg]
  true)

(defn check-axiom-3-and-4
  "Strokes send arrows only to nodes. Nodes send arrows only to strokes."
  [jg]
  (every? (fn [[start end]]
            (cond (stroke? jg start) (node? jg end)
                  (node? jg start) (stroke? jg end)
                  :else nil))
          (graph/edges (:graph jg))))

(defn check-axiom-5
  "Every stroke sends an arrow to exactly one thing."
  [jg]
  (every? (fn [stroke] (= 1 (count (jgout jg stroke))))
          (strokes jg)))

(defn check-axiom-6
  "Arrowing is one-way."
  [jg]
  (every? (fn [[n-or-s1 n-or-s2]]
            (not (graph/has-edge? (:graph jg) n-or-s2 n-or-s1)))
          (graph/edges (:graph jg))))

(defn check-axiom-7
  "If two strokes send arrows to the same thing, and the things from
  which one of them receives arrows are among those from which the
  other receives arrows, then those strokes are identical."
  [jg]
  (let [ss (strokes jg)]
    (every? (fn [s] (every? (fn [s2] (= s s2))
                            ;; find strokes s2 where s2's incoming
                            ;; arrows are subseteq of incoming arrows
                            ;; of s
                            (filter (fn [s2]
                                      (and (not-empty (jgin jg s))
                                           (not-empty (jgin jg s2))
                                           (every? (set (jgin jg s)) (jgin jg s2))))
                                    ;; find strokes that have an arrow to the same node
                                    (filter (fn [s2] (= (first (jgout jg s))
                                                        (first (jgout jg s2))))
                                            ss))))
            ss)))

(defn check-axiom-8
  "Every node receives an arrow."
  [jg]
  (every? (fn [node] (not-empty (jgin jg node)))
          (nodes jg)))

(defn check-axiom-coloration-1
  "Every black node receives an arrow from some black inference stroke."
  [jg]
  (every? (fn [node] (or (white? jg node)
                         (some (fn [in] (and (stroke? jg in) (black? jg in)))
                               (jgin jg node))))
          (nodes jg)))

(defn check-axiom-coloration-2
  "Every white node receives arrows only from white inference strokes."
  [jg]
  (every? (fn [node] (or (black? jg node)
                         (every? (fn [in] (and (stroke? jg in)
                                               (white? jg in)))
                                 (jgin jg node))))
          (nodes jg)))

(defn check-axiom-coloration-3
  "Every black inference stroke receives arrows (if any) only from black nodes."
  [jg]
  (every? (fn [stroke] (or (white? jg stroke)
                           (empty? (jgin jg stroke))
                           (every? (fn [n] (and (node? jg n) (black? jg n)))
                                   (jgin jg stroke))))
          (strokes jg)))

(defn check-axiom-coloration-4
  "Every white inference stroke that receives an arrow receives an arrow from some white node."
  [jg]
  (every? (fn [stroke] (or (black? jg stroke)
                           (empty? (jgin jg stroke))
                           (some (fn [in] (and (node? jg in)
                                               (white? jg in)))
                                 (jgin jg stroke))))
          (strokes jg)))

(defn check-axiom-coloration-bottom
  "The node 'bottom' is white."
  [jg]
  (or (not (node? jg :bottom)) (white? jg :bottom)))

(defn check-structure-axioms-debug
  [jg]
  (and (or (check-axiom-neg1 jg) (println "Fails Axiom -1."))
       (or (check-axiom-0 jg) (println "Fails Axiom 0."))
       (or (check-axiom-1 jg) (println "Fails Axiom 1."))
       (or (check-axiom-2 jg) (println "Fails Axiom 2."))
       (or (check-axiom-3-and-4 jg) (println "Fails Axioms 3/4."))
       (or (check-axiom-5 jg) (println "Fails Axiom 5."))
       (or (check-axiom-6 jg) (println "Fails Axiom 6."))
       (or (check-axiom-7 jg) (println "Fails Axiom 7."))
       (or (check-axiom-8 jg) (println "Fails Axiom 8."))))

(defn check-color-axioms-debug
  [jg]
  (and (or (check-axiom-coloration-1 jg) (println "Fails Axiom of Coloration 1."))
       (or (check-axiom-coloration-2 jg) (println "Fails Axiom of Coloration 2."))
       (or (check-axiom-coloration-3 jg) (println "Fails Axiom of Coloration 3."))
       (or (check-axiom-coloration-4 jg) (println "Fails Axiom of Coloration 4."))
       (or (check-axiom-coloration-bottom jg) (println "Fails Axiom of Coloration Bottom."))))

(defn check-structure-axioms
  [jg]
  (if @debugging?
    (check-structure-axioms-debug jg)
    (and (check-axiom-neg1 jg)
         (check-axiom-0 jg)
         (check-axiom-1 jg)
         (check-axiom-2 jg)
         (check-axiom-3-and-4 jg)
         (check-axiom-5 jg)
         (check-axiom-6 jg)
         (check-axiom-7 jg)
         (check-axiom-8 jg))))

(defn check-color-axioms
  [jg]
  (if @debugging?
    (check-color-axioms-debug jg)
    (and (check-axiom-coloration-1 jg)
         (check-axiom-coloration-2 jg)
         (check-axiom-coloration-3 jg)
         (check-axiom-coloration-4 jg)
         (check-axiom-coloration-bottom jg))))
