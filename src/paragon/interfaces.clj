(ns paragon.interfaces
  (:require [paragon.core :refer :all]
            [paragon.coloring :refer :all]
            [clojure.string :as str]
            [clojure.java.shell :as shell]
            [clojure.math.combinatorics :as combo]))

;;;;
;;;; INTERFACING WITH "Changes of Mind" (Tennant, 2012)
;;;;

(defn convert-to-com-input
  [fdn contract-ns]
  (format "%s\n\n[%s] ?- [%s]."
          (str/join "\n" (for [n (nodes fdn)]
                           (format "node(%s)." (fdnstr n))))
          (str/join ", " (for [n (nodes fdn)
                               s (fdnin fdn n)]
                           (if (empty? (fdnin fdn s))
                             (format "[[%s], %s]" (fdnstr n) (fdnstr n))
                             (format "[[%s], %s]" (str/join ", " (map fdnstr (fdnin fdn s))) (fdnstr n)))))
          (str/join "," (map fdnstr contract-ns))))

(defn parse-com-output
  [fdn output]
  (spread-color
   (reduce (fn [fdn [initials conclusion]]
             (if (= initials conclusion)
               (-> fdn (assert-black (format "s%s" conclusion))
                   (assert-black conclusion))
               (reduce assert-black fdn (conj (str/split initials #"\s*,\s*") conclusion))))
           (reduce assert-white fdn (concat (nodes fdn) (strokes fdn)))
           (map #(str/split % #"\s*\|-\s*")
                (re-seq #"[\w,]+ \|- \w+" (second (re-find #"(?s)ANSWER: (.*?)####" output)))))))

(defn process-with-com
  [fdn contract-ns mm?]
  (let [input-str (convert-to-com-input fdn contract-ns)]
    (when @debugging? (println input-str))
    (spit "test-com.pl" input-str)
    (let [{output :out} (shell/sh "changes-of-mind/a.out" "test-com.pl" (if mm? "on" "off"))]
      (when @debugging? (println output))
      (try (parse-com-output fdn output)
           (catch Exception _ (println input-str) (println output) (throw (Exception.)))))))

;;;;
;;;; PROLOG OUTPUT
;;;;

(defn convert-to-prolog
  [fdn]
  (let [rules (for [n (nodes fdn)
                    :when (and (not= n :bottom) (not (initial? fdn n)))
                    s (fdnin fdn n)]
                {:head n :body (fdnin fdn s)})
        inconsistencies (reduce (fn [m s]
                                  (let [incon (fdnin fdn s)]
                                    (reduce (fn [m2 n]
                                              (update-in m2 [n] conj (filter #(not= n %) incon)))
                                            m incon)))
                                {} (fdnin fdn :bottom))
        preds (concat (map #(format "initial(%s)." (fdnstr %))
                           (filter #(initial? fdn %) (nodes fdn)))
                      (map #(format "b(%s)." (fdnstr %))
                           (filter #(initial? fdn %) (believed fdn)))
                      (map (fn [rule]
                             (let [rule-body (map #(format "believed(%s)" (fdnstr %))
                                                  (:body rule))]
                               (format "believed(%s) :- %s."
                                       (fdnstr (:head rule)) (str/join ", " rule-body))))
                           rules)
                      (mapcat (fn [[n incon-groups]]
                                (map (fn [incon-group]
                                       (format "consistent(%s) :- %s."
                                               (fdnstr n)
                                               (str/join ", " (map (fn [incon] (format "disbelieved(%s)" (fdnstr incon)))
                                                                   incon-group))))
                                     (apply combo/cartesian-product incon-groups)))
                              (seq inconsistencies))
                      ;; all nodes not mentioned in inconsistencies map get default consistency
                      (map (fn [n] (format "consistent(%s)." (fdnstr n)))
                           (filter (fn [n] (and (not= :bottom n) (nil? (inconsistencies n)))) (nodes fdn)))
                      ["assertwhite(X) :- retract(b(X))."
                       "assertblack(X) :- initial(X), assert(b(X)), allconsistent.\nassertblack(X) :- initial(X), retract(b(X))."
                       "believed(X) :- initial(X), b(X)."
                       "disbelieved(X) :- \\+b(X)."
                       "allconsistent :- forall(believed(X), consistent(X))."])]
    (str
      ":- dynamic b/1.\n"
      (str/join "\n" (sort preds)))))


