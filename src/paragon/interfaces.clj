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
  [jg contract-ns]
  (format "%s\n\n[%s] ?- [%s]."
          (str/join "\n" (for [n (nodes jg)]
                           (format "node(%s)." (jgstr n))))
          (str/join ", " (for [n (nodes jg)
                               s (jgin jg n)]
                           (if (empty? (jgin jg s))
                             (format "[[%s], %s]" (jgstr n) (jgstr n))
                             (format "[[%s], %s]" (str/join ", " (map jgstr (jgin jg s))) (jgstr n)))))
          (str/join "," (map jgstr contract-ns))))

(defn parse-com-output
  [jg output]
  (spread-black
   (reduce (fn [jg [initials conclusion]]
             (if (= initials conclusion)
               (-> jg (assert-black (format "s%s" conclusion))
                   (assert-black conclusion))
               (reduce assert-black jg (conj (str/split initials #"\s*,\s*") conclusion))))
           (reduce assert-white jg (concat (nodes jg) (strokes jg)))
           (map #(str/split % #"\s*\|-\s*")
                (re-seq #"[\w,]+ \|- \w+" (second (re-find #"(?s)ANSWER: (.*?)####" output)))))))

(defn process-with-com
  [jg contract-ns mm?]
  (let [input-str (convert-to-com-input jg contract-ns)]
    (when @debugging? (println input-str))
    (spit "test-com.pl" input-str)
    (let [{output :out} (shell/sh "changes-of-mind/a.out" "test-com.pl" (if mm? "on" "off"))]
      (when @debugging? (println output))
      (try (parse-com-output jg output)
           (catch Exception _ (println input-str) (println output) (throw (Exception.)))))))

;;;;
;;;; PROLOG OUTPUT
;;;;

(defn convert-to-prolog
  [jg]
  (let [rules (for [n (nodes jg)
                    :when (and (not= n :bottom) (not (initial? jg n)))
                    s (jgin jg n)]
                {:head n :body (jgin jg s)})
        inconsistencies (reduce (fn [m s]
                                  (let [incon (jgin jg s)]
                                    (reduce (fn [m2 n]
                                              (update-in m2 [n] conj (filter #(not= n %) incon)))
                                            m incon)))
                                {} (jgin jg :bottom))
        preds (concat (map #(format "initial(%s)." (jgstr %))
                           (filter #(initial? jg %) (nodes jg)))
                      (map #(format "b(%s)." (jgstr %))
                           (filter #(initial? jg %) (believed jg)))
                      (map (fn [rule]
                             (let [rule-body (map #(format "believed(%s)" (jgstr %))
                                                  (:body rule))]
                               (format "believed(%s) :- %s."
                                       (jgstr (:head rule)) (str/join ", " rule-body))))
                           rules)
                      (mapcat (fn [[n incon-groups]]
                                (map (fn [incon-group]
                                       (format "consistent(%s) :- %s."
                                               (jgstr n)
                                               (str/join ", " (map (fn [incon] (format "disbelieved(%s)" (jgstr incon)))
                                                                   incon-group))))
                                     (apply combo/cartesian-product incon-groups)))
                              (seq inconsistencies))
                      ;; all nodes not mentioned in inconsistencies map get default consistency
                      (map (fn [n] (format "consistent(%s)." (jgstr n)))
                           (filter (fn [n] (and (not= :bottom n) (nil? (inconsistencies n)))) (nodes jg)))
                      ["assertwhite(X) :- retract(b(X))."
                       "assertblack(X) :- initial(X), assert(b(X)), allconsistent.\nassertblack(X) :- initial(X), retract(b(X))."
                       "believed(X) :- initial(X), b(X)."
                       "disbelieved(X) :- \\+b(X)."
                       "allconsistent :- forall(believed(X), consistent(X))."])]
    (str
      ":- dynamic b/1.\n"
      (str/join "\n" (sort preds)))))


