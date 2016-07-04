(ns paragon.dbcompletion
  (:require [paragon.core :refer :all]
            [paragon.coloring :refer :all]
            [clojure.math.combinatorics :refer [combinations]]
            [clojure.java.io :as io]
            [clojure.data.csv :as csv]
            [clojure.string :as str]
            [clojure.pprint]))

(defn compile-relations
  [headers rows]
  ;; assumption: each row is the same length
  (let [idxs (range (count headers))]
    (reduce (fn [m row]
              (reduce (fn [m2 col-idx]
                        (let [header (nth headers col-idx)
                              cell (nth row col-idx)]
                          (reduce (fn [m3 col-idx2]
                                    (let [header2 (nth headers col-idx2)
                                          cell2 (nth row col-idx2)
                                          prior (get-in m3 [cell header2] #{})]
                                      (assoc-in m3 [cell header2] (conj prior cell2))))
                                  m2 (filter #(not= col-idx %) idxs))))
                      m idxs))
            {} rows)))

(defn compile-inconsistencies
  [rows-prefixed synonyms]
  ;; synonyms should be a coll of sets
  (let [synonyms-map (reduce (fn [m syns]
                               (reduce (fn [m2 syn]
                                         (assoc m2 syn (disj syns syn)))
                                       m syns))
                             {} synonyms)]
    (doall (for [idx (range (count (first rows-prefixed)))]
             (filter (fn [[x y]] (and (not= x y)
                                      (or (nil? (get synonyms-map x))
                                          (not ((get synonyms-map x) y)))))
                     (combinations (set (map #(nth % idx) rows-prefixed)) 2))))))

(defn build-fdn-from-headers-rows
  [headers rows synonyms]
  (let [rows-prefixed (map (fn [row] (vec (map (fn [idx] (format "%s:%s" (nth headers idx) (nth row idx)))
                                               (range (count headers)))))
                           rows)
        relations (compile-relations headers rows-prefixed)
        inconsistencies (compile-inconsistencies rows-prefixed synonyms)
        fdn (reduce (fn [fdn [k rels]]
                      (reduce (fn [fdn2 [rel-key rel-vals]]
                                (if (and (= 1 (count rel-vals))
                                         (= 2 (count (str/split (first rel-vals) #":")))) ;; make sure there is a cell value
                                  (can-explain fdn2 [k] (vec rel-vals))
                                  fdn2))
                              (add-initial fdn k) rels))
                    (new-fdn)
                    (filter #(= 2 (count (str/split (first %) #":"))) ;; make sure there is a cell value
                            (seq relations)))]
    fdn))
(comment
  (reduce (fn [fdn incon] (add-inconsistencies fdn [incon]))
          fdn inconsistencies))

(defn build-fdn-from-csv
  [fname column-indexes synonyms]
  (let [data (with-open [in (io/reader fname)]
               (doall (map (fn [row] (vec (map (fn [idx] (nth row idx)) column-indexes)))
                           (csv/read-csv in))))]
    (build-fdn-from-headers-rows (vec (first data)) (rest data) synonyms)))


