(ns paragon.builders
  (:require [paragon.core :refer :all]
            [paragon.coloring :refer :all]
            [loom.graph :as graph]
            [loom.alg :as alg]
            [clojure.string :as str]
            [clojure.pprint]))

;;;;
;;;; GRAPHS FROM COMPLEX QUERIES
;;;;

(defn simplify-nested-vec-1
  [vs]
  ;; look through every step in the nested-vec vs
  (loop [subvs (map (fn [[ps c & _]] [ps c]) vs) ;; ignore :hide third element
         new-vs []]
    (if (empty? subvs)
      ;; done looking through steps; return result
      new-vs
      (let [v (first subvs) ;; extract next step
            premises (first v)
            conclusion (second v)]
        ;; if there is exactly one premise (and this doesn't point to :bottom)
        (if (and (= 1 (count premises)) (not= :bottom conclusion))
          (let [premise (first premises)
                ;; find steps with sole premise as related step's conclusion
                conclusion-steps (filter (fn [[ps c & _]] (= c premise)) vs)
                ;; find steps with conclusion as part of related step's premises
                premise-steps (filter (fn [[ps _ & _]] (some #(= % conclusion) ps)) vs)]
            ;; if there is only one such related step, drop this step
            (cond (and (= 1 (count conclusion-steps)) (= 1 (count premise-steps)))
                  ;; drop this step, it's redundant; and rewrite related step
                  (do (when @debugging? (println "Simplifying nested vec (1) by removing" v))
                      (simplify-nested-vec-1
                       (conj (filter #(and (not= % (first conclusion-steps)) (not= % v))
                                     vs)
                             [(first (first conclusion-steps)) conclusion])))
                  ;; otherwise, keep this step
                  :else
                  (recur (rest subvs) (conj new-vs v))))
          ;; else, there is more than one premise; keep it
          (recur (rest subvs) (conj new-vs v)))))))

(defn simplify-nested-vec-2
  [vs]
  ;; look through every step in the nested-vec vs
  (loop [subvs (map (fn [[ps c & _]] [ps c]) vs) ;; ignore :hide third element
         new-vs []]
    (if (empty? subvs)
      ;; done looking through steps; return result
      new-vs
      (let [v (first subvs) ;; extract next step
            premises (first v)
            conclusion (second v)]
        ;; if there is exactly one premise (and this doesn't point to :bottom)
        (if (and (= 1 (count premises)) (not= :bottom conclusion))
          (let [premise (first premises)
                conclusion-steps (filter (fn [[_ c & _]] (= c conclusion)) vs)
                ;; find steps with conclusion as part of related step's premises
                premise-steps (filter (fn [[ps _ & _]] (some #(= % conclusion) ps)) vs)]
            ;; if there is only one such related step, drop this step
            (cond
              ;; check if this steps conclusion only appears in a
              ;; single step's premises; if so, we can replace
              ;; that occurrence of this step's conclusion with
              ;; its premise
              (and (= 1 (count premise-steps)) (= 1 (count conclusion-steps)))
              ;; drop this step, it's redundant; and rewrite related step
              (do (when @debugging? (println "Simplifying nested vec (2) by removing" v))
                  (simplify-nested-vec-2
                   (conj (filter #(and (not= % (first premise-steps)) (not= % v))
                                 vs)
                         [(vec (conj (filter #(not= % conclusion) (first (first premise-steps)))
                                     premise))
                          (second (first premise-steps))])))
              ;; otherwise, keep this step
              :else
              (recur (rest subvs) (conj new-vs v))))
          ;; else, there is more than one premise; keep it
          (recur (rest subvs) (conj new-vs v)))))))

(defn simplify-nested-vec
  [vs]
  (simplify-nested-vec-2 (simplify-nested-vec-1 vs)))

(defn build-nested-vec-rec
  [query id]
  (if (not (or (vector? query) (list? query) (seq? query)))
    [[[query] id]]
    (let [[sub-vecs ids] (loop [id (inc id) ids [] subquery (rest query) sub-vecs []]
                           (if (empty? subquery)
                             [sub-vecs (vec (sort (set ids)))]
                             (let [sv (build-nested-vec-rec (first subquery) id)
                                   new-ids (mapcat (fn [[ps c & _]] (filter integer? (conj ps c))) sv)]
                               (recur (inc (apply max new-ids))
                                      (conj ids id)
                                      (rest subquery)
                                      (concat sub-vecs sv)))))
          immediate-ids (vec (take (count (rest query)) ids))
          next-id (inc (apply max ids))]
      (case (first query)
        "OR"
        (vec (concat sub-vecs (map (fn [im-id] [[im-id] id]) immediate-ids)))
        "AND"
        (conj sub-vecs [immediate-ids id])
        "NOT"
        (let [im-id (first immediate-ids)]
          (conj (vec (for [[ps c & _] sub-vecs]
                       (if (= c im-id)
                         [ps c :hide]
                         [ps c])))
                [[im-id next-id] :bottom]
                [[next-id] id]))
        []))))

(defn add-nested-vec
  "Add nodes/strokes as defined from a nested vector structure, e.g.: [[[a b] c] [[d] e]]."
  [fdn v]
  (let [fdn2 (reduce (fn [fdn [premises conclusion]]
                      (let [stroke (format "S%s__%s" (str/join "_" (map fdnstr premises)) (fdnstr conclusion))]
                        (-> fdn
                            (forall-just premises stroke)
                            (exists-just [stroke] conclusion))))
                    fdn v)]
    (apply add-initial fdn2 (filter #(empty? (fdnin fdn2 %)) (nodes fdn2)))))

(defn build-from-query
  [query goal-nodes]
  (let [fdn (new-fdn)
        nested-vec (build-nested-vec-rec query 1)
        nested-vec-goals (vec (concat nested-vec (for [goal goal-nodes] [[1] goal])))
        simp-nested-vec-goals (simplify-nested-vec nested-vec-goals)
        fdn-added (add-nested-vec fdn simp-nested-vec-goals)]
    (when @debugging?
      (println "Nested vec:" (with-out-str (clojure.pprint/pprint nested-vec)))
      (println "Nested vec goals:" (with-out-str (clojure.pprint/pprint nested-vec-goals)))
      (println "Simplified nested vec goals:" (with-out-str (clojure.pprint/pprint simp-nested-vec-goals))))
    ;; set initial black nodes for NOT operators
    (spread-black
     (reduce assert-black-initial fdn-added (filter #(and (number? %) (initial? fdn-added %)) (nodes fdn-added))))))

;;;;
;;;; RANDOM GENERATION
;;;;

(defn split-vec
  [v chance-split]
  (let [v-count (count v)]
    (if (= 1 v-count)
      [[v]]
      (let [splits (filter (fn [_] (> chance-split (rand))) (range v-count))
            v-groups (doall (filter not-empty (map (fn [i j] (subvec v i j))
                                                   (concat [0] splits)
                                                   (concat splits [v-count]))))]
        #_(prn "v" v "splits" splits "v-groups" v-groups)
        (filter (fn [[v1 v2]] (and (not (empty? v1)) (not (empty? v2))))
                (partition 2 (interleave v-groups (rest v-groups))))))))

(defn remove-bad-stroke
  [fdn]
  (let [ss (strokes fdn)
        bad-stroke (first (filter (fn [s] (some (fn [s2]
                                                  (and (not= s s2)
                                                       ;; find strokes s2 that have an arrow
                                                       ;; to the same node
                                                       (= (first (fdnout fdn s))
                                                          (first (fdnout fdn s2)))
                                                       ;; and where s2's incoming arrows
                                                       ;; are subseteq of incoming arrows of s
                                                       (not-empty (fdnin fdn s))
                                                       (not-empty (fdnin fdn s2))
                                                       (every? (set (fdnin fdn s)) (fdnin fdn s2))))
                                                ss))
                                  ss))]
    (when bad-stroke
      (remove-node-or-stroke fdn bad-stroke))))

(defn remove-inaccessible
  [fdn]
  (let [accessible (set (alg/pre-traverse (graph/graph (:graph fdn)) (first (shuffle (graph/nodes (:graph fdn))))))]
    (reduce remove-node-or-stroke fdn (filter #(not (accessible %)) (graph/nodes (:graph fdn))))))

(defn gen-random-andor-graph
  [node-count chance-split chance-and inconsistent-count]
  (let [node-options (vec (map str (range node-count)))
        node-groups (split-vec node-options chance-split)
        node-groups-squared (mapcat (fn [[ns1 ns2]] (split-vec (vec (concat ns1 ns2)) chance-split))
                                    node-groups)
        node-groups-cubed (mapcat (fn [[ns1 ns2]] (split-vec (vec (concat ns1 ns2)) chance-split))
                                  node-groups-squared)
        paired (map (fn [ng] (concat ng (if (> chance-and (rand)) [:forall-just] [:exists-just])))
                    node-groups-cubed)
        fdn (new-fdn)
        fdn2 (reduce (fn [fdn [node-group1 node-group2 linktype]]
                      #_(prn node-group1 node-group2 linktype)
                      (if (= :forall-just linktype)
                        (reduce (fn [fdn n] (-> fdn (forall-just node-group1 (format "s%s" n))
                                               (exists-just [(format "s%s" n)] n)))
                                fdn node-group2)
                        (reduce (fn [fdn n1]
                                  (reduce (fn [fdn n2]
                                            (-> fdn (forall-just [n1] (format "s%s_%s" n1 n2))
                                                (exists-just [(format "s%s_%s" n1 n2)] n2)))
                                          fdn node-group2))
                                fdn node-group1)))
                    fdn paired)
        top-nodes (filter (fn [n] (empty? (graph/incoming (:graph fdn2) n)))
                          (nodes fdn2))
        fdn-premises (reduce (fn [fdn n] (exists-just fdn [(format "s%s" n)] n))
                            fdn2 top-nodes)
        fdn-inconsistencies (apply add-inconsistencies fdn-premises
                                  (take inconsistent-count
                                        (shuffle (for [n1 (nodes fdn-premises)
                                                       n2 (shuffle (nodes fdn-premises))
                                                       :when (not= n1 n2)]
                                                   [n1 n2]))))
        fdn-accessible (remove-inaccessible fdn-inconsistencies)
        ;; find strokes that fail axiom 7
        fdn-fixed (loop [fdn fdn-accessible]
                   (if-let [fdn2 (remove-bad-stroke fdn)]
                     (recur fdn2) fdn))]
    (remove-inaccessible fdn-fixed)))

