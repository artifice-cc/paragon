(ns paragon.axioms
  (:require [paragon.core :refer :all])
  (:require [loom.graph :as graph]))

(defn check-axiom-neg1
  "Everything is black or white."
  [fdn]
  (every? #{:white :black} (vals (:coloring fdn))))

(defn check-axiom-0
  "Nothing is both black and white.

  Axiom 0 is confirmed from the fact that :coloring is a map."
  [fdn]
  true)

(defn check-axiom-1
  [fdn]
  "Everything is either a node or a stroke."
  (every? #{:node :stroke} (vals (:types fdn))))

(defn check-axiom-2
  "Nothing is both a node and a stroke.

  Axiom 2 is confirmed from the fact that :types is a map."
  [fdn]
  true)

(defn check-axiom-3-and-4
  "Strokes send arrows only to nodes. Nodes send arrows only to strokes."
  [fdn]
  (every? (fn [[start end]]
            (cond (stroke? fdn start) (node? fdn end)
                  (node? fdn start) (stroke? fdn end)
                  :else nil))
          (graph/edges (:graph fdn))))

(defn check-axiom-5
  "Every stroke sends an arrow to exactly one thing."
  [fdn]
  (every? (fn [stroke] (= 1 (count (fdnout fdn stroke))))
          (strokes fdn)))

(defn check-axiom-6
  "Arrowing is one-way."
  [fdn]
  (every? (fn [[n-or-s1 n-or-s2]]
            (not (graph/has-edge? (:graph fdn) n-or-s2 n-or-s1)))
          (graph/edges (:graph fdn))))

(defn check-axiom-7
  "If two strokes send arrows to the same thing, and the things from
  which one of them receives arrows are among those from which the
  other receives arrows, then those strokes are identical."
  [fdn]
  (let [ss (strokes fdn)]
    (every? (fn [s] (every? (fn [s2] (= s s2))
                            ;; find strokes s2 where s2's incoming
                            ;; arrows are subseteq of incoming arrows
                            ;; of s
                            (filter (fn [s2]
                                      (and (not-empty (fdnin fdn s))
                                           (not-empty (fdnin fdn s2))
                                           (every? (set (fdnin fdn s)) (fdnin fdn s2))))
                                    ;; find strokes that have an arrow to the same node
                                    (filter (fn [s2] (= (first (fdnout fdn s))
                                                        (first (fdnout fdn s2))))
                                            ss))))
            ss)))

(defn check-axiom-8
  "Every node receives an arrow."
  [fdn]
  (every? (fn [node] (not-empty (fdnin fdn node)))
          (nodes fdn)))

(defn check-axiom-coloration-1
  "Every black node receives an arrow from some black inference stroke."
  [fdn]
  (when @debugging?
    (let [failed (filter (comp not second)
                         (map (fn [node] [node (or (white? fdn node)
                                                   (some (fn [in] (and (stroke? fdn in) (black? fdn in)))
                                                         (fdnin fdn node)))])
                              (nodes fdn)))]
      (when (not-empty failed)
        (warning "Fails Axiom of Coloration 1 (every black node receives an arrow from some black inference stroke):" (map first failed)))))
  (every? (fn [node] (or (white? fdn node)
                         (some (fn [in] (and (stroke? fdn in) (black? fdn in)))
                               (fdnin fdn node))))
          (nodes fdn)))

(defn check-axiom-coloration-2
  "Every white node receives arrows only from white inference strokes."
  [fdn]
  (when @debugging?
    (let [failed (filter (comp not second)
                         (map (fn [node] [node (or (black? fdn node)
                                                   (every? (fn [in] (and (stroke? fdn in)
                                                                         (white? fdn in)))
                                                           (fdnin fdn node)))])
                              (nodes fdn)))]
      (when (not-empty failed)
        (warning "Fails Axiom of Coloration 2 (every white node receives arrows only from white inference strokes):" (map first failed)))))
  (every? (fn [node] (or (black? fdn node)
                         (every? (fn [in] (and (stroke? fdn in)
                                               (white? fdn in)))
                                 (fdnin fdn node))))
          (nodes fdn)))

(defn check-axiom-coloration-3
  "Every black inference stroke receives arrows (if any) only from black nodes."
  [fdn]
  (when @debugging?
    (let [failed (filter (comp not second)
                         (map (fn [stroke] [stroke (or (white? fdn stroke)
                                                       (empty? (fdnin fdn stroke))
                                                       (every? (fn [n] (and (node? fdn n) (black? fdn n)))
                                                               (fdnin fdn stroke)))])
                              (strokes fdn)))]
      (when (not-empty failed)
        (warning "Fails Axiom of Coloration 3 (every black inference stroke receives arrows (if any) only from black nodes):" (map first failed)))))
  (every? (fn [stroke] (or (white? fdn stroke)
                           (empty? (fdnin fdn stroke))
                           (every? (fn [n] (and (node? fdn n) (black? fdn n)))
                                   (fdnin fdn stroke))))
          (strokes fdn)))

(defn check-axiom-coloration-4
  "Every white inference stroke that receives an arrow receives an arrow from some white node."
  [fdn]
  (when @debugging?
    (let [failed (filter (comp not second)
                         (map (fn [stroke] [stroke (or (black? fdn stroke)
                                                       (empty? (fdnin fdn stroke))
                                                       (some (fn [in] (and (node? fdn in)
                                                                           (white? fdn in)))
                                                             (fdnin fdn stroke)))])
                              (strokes fdn)))]
      (when (not-empty failed)
        (warning "Fails Axiom of Coloration 4 (every white inference stroke that receives an arrow receives an arrow from some white node):" (map first failed)))))
  (every? (fn [stroke] (or (black? fdn stroke)
                           (empty? (fdnin fdn stroke))
                           (some (fn [in] (and (node? fdn in)
                                               (white? fdn in)))
                                 (fdnin fdn stroke))))
          (strokes fdn)))

(defn check-axiom-coloration-bottom
  "The node 'bottom' is white."
  [fdn]
  (or (not (node? fdn :bottom)) (white? fdn :bottom)))

(defn check-structure-axioms-debug
  [fdn]
  (and (or (check-axiom-neg1 fdn) (warning "Fails Axiom -1."))
       (or (check-axiom-0 fdn) (warning "Fails Axiom 0."))
       (or (check-axiom-1 fdn) (warning "Fails Axiom 1."))
       (or (check-axiom-2 fdn) (warning "Fails Axiom 2."))
       (or (check-axiom-3-and-4 fdn) (warning "Fails Axioms 3/4."))
       (or (check-axiom-5 fdn) (warning "Fails Axiom 5."))
       (or (check-axiom-6 fdn) (warning "Fails Axiom 6."))
       (or (check-axiom-7 fdn) (warning "Fails Axiom 7."))
       (or (check-axiom-8 fdn) (warning "Fails Axiom 8."))))

(defn check-color-axioms-debug
  [fdn]
  (and (or (check-axiom-coloration-1 fdn) (warning "Fails Axiom of Coloration 1."))
       (or (check-axiom-coloration-2 fdn) (warning "Fails Axiom of Coloration 2."))
       (or (check-axiom-coloration-3 fdn) (warning "Fails Axiom of Coloration 3."))
       (or (check-axiom-coloration-4 fdn) (warning "Fails Axiom of Coloration 4."))
       (or (check-axiom-coloration-bottom fdn) (warning "Fails Axiom of Coloration Bottom."))))

(defn check-structure-axioms
  [fdn]
  (if @debugging?
    (check-structure-axioms-debug fdn)
    (and (check-axiom-neg1 fdn)
         (check-axiom-0 fdn)
         (check-axiom-1 fdn)
         (check-axiom-2 fdn)
         (check-axiom-3-and-4 fdn)
         (check-axiom-5 fdn)
         (check-axiom-6 fdn)
         (check-axiom-7 fdn)
         (check-axiom-8 fdn))))

(defn check-color-axioms
  [fdn]
  (if @debugging?
    (check-color-axioms-debug fdn)
    (and (check-axiom-coloration-1 fdn)
         (check-axiom-coloration-2 fdn)
         (check-axiom-coloration-3 fdn)
         (check-axiom-coloration-4 fdn)
         (check-axiom-coloration-bottom fdn))))
