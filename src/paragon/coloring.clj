(ns paragon.coloring
  (:require [paragon.core :refer :all]
            [paragon.axioms :refer :all]
            [paragon.strategies :refer :all]))

(defn assert-color
  [jg stroke-or-node color]
  (when @debugging? (println "asserting" stroke-or-node "as" color))
  (assoc-in jg [:coloring stroke-or-node] color))

(defn assert-black
  [jg stroke-or-node]
  (assert-color jg stroke-or-node :black))

(defn assert-black-initial
  [jg node]
  (-> jg (assert-black node) (assert-black (format ".%s" (jgstr node)))))

(defn assert-white
  [jg stroke-or-node]
  (assert-color jg stroke-or-node :white))


(defn spread-white-bad-strokes
  "Bad stroke w.r.t. white: A stroke is black but points a white node, or
  a stroke is black but some white node points to it."
  [jg]
  (filter (fn [s] (and (black? jg s)
                       (or (white? jg (first (jgout jg s)))
                           (some (fn [n] (white? jg n)) (jgin jg s)))))
          (strokes jg)))

(defn spread-white-bad-nodes-deterministic
  "Bad node w.r.t. white (deterministic): A node is black but all of its incoming strokes are white."
  [jg]
  (filter (fn [n] (and (black? jg n)
                       (every? (fn [s] (white? jg s)) (jgin jg n))))
          (nodes jg)))

(defn spread-white-bad-nodes-nondeterministic
  "Bad node w.r.t. white (non-deterministic): A node is black but points to a white stroke that
  has only black nodes pointing to it."
  [jg]
  (filter (fn [n] (and (black? jg n)
                       (some (fn [s] (and (white? jg s)
                                          (every? (fn [n2] (black? jg n2)) (jgin jg s))))
                             (jgout jg n))))
          (nodes jg)))

(defn spread-white
  [jg white-strategy]
  (loop [jg jg]
    (if (check-color-axioms jg)
      ;; nothing to do, everything checks out
      (do (when @debugging? (println "All axioms satisfied in spread-white.\n\n"))
          jg)
      ;; something to do (inconsistent), spread white
      (let [bad-strokes (delay (spread-white-bad-strokes jg))
            bad-nodes-deterministic (delay (spread-white-bad-nodes-deterministic jg))
            bad-nodes-nondeterministic (delay (spread-white-bad-nodes-nondeterministic jg))]
        (when @debugging?
          (println "Spreading white.")
          (println "Found bad strokes:" @bad-strokes)
          (println "Found bad nodes (deterministic):" @bad-nodes-deterministic)
          (println "Found bad nodes (non-deterministic):" @bad-nodes-nondeterministic))
        (cond
          ;; if we have bad strokes, just take care of them; no need for strategy
          ;; or, if we have deterministic bad nodes, just take care of them; no need for strategy
          (or (not-empty @bad-strokes) (not-empty @bad-nodes-deterministic))
          (recur (reduce assert-white jg (concat @bad-strokes @bad-nodes-deterministic)))
          ;; if we have a non-deterministic bad node, employ the strategy
          (not-empty @bad-nodes-nondeterministic)
          (recur (assert-white jg (white-strategy jg @bad-nodes-nondeterministic)))
          :else
          (do (when @debugging? (println "Axioms failed in spread-white."))
              jg))))))

(defn spread-abduce-bad-strokes-deterministic
  "Bad stroke w.r.t. abduction (deterministic): A stroke is white but all its incoming nodes are black."
  [jg]
  (filter (fn [s] (and (white? jg s)
                       (and (not-empty (jgin jg s))
                            (every? (fn [n] (black? jg n))
                                    (jgin jg s)))))
          (strokes jg)))

(defn spread-abduce-bad-strokes-nondeterministic
  "Bad stroke w.r.t. abduction (non-deterministic): A stroke is white but points to a black node that
  has only white strokes pointing to it."
  [jg]
  (filter (fn [s] (and (white? jg s)
                       (black? jg (first (jgout jg s)))
                       (every? (fn [s2] (white? jg s2))
                               (jgin jg (first (jgout jg s))))))
          (strokes jg)))

(defn spread-abduce-bad-nodes
  "Bad node w.r.t. abduction: A node is white but is pointed to by a black stroke or points to a black stroke."
  [jg]
  (filter (fn [n] (and (white? jg n)
                       (or (some (fn [s] (black? jg s)) (jgin jg n))
                           (some (fn [s] (black? jg s)) (jgout jg n)))))
          (nodes jg)))

(defn spread-abduce
  [jg abduce-strategy]
  (loop [jg jg]
    (if (check-color-axioms jg)
      ;; nothing to do, everything checks out
      (do (when @debugging? (println "All axioms satisfied in spread-abduce.\n\n"))
          jg)
      ;; something to do (inconsistent), spread abductively
      (let [bad-strokes-deterministic (delay (spread-abduce-bad-strokes-deterministic jg))
            bad-strokes-nondeterministic (delay (spread-abduce-bad-strokes-nondeterministic jg))
            bad-nodes (delay (spread-abduce-bad-nodes jg))]
        (when @debugging?
          (println "Spreading abductively.")
          (println "Found bad strokes (deterministic):" @bad-strokes-deterministic)
          (println "Found bad strokes (non-deterministic):" @bad-strokes-nondeterministic)
          (println "Found bad nodes:" @bad-nodes))
        (cond
          ;; if we have deterministic bad strokes and/or nodes, just take care of them; no need for strategy
          (or (not-empty @bad-strokes-deterministic) (not-empty @bad-nodes))
          (recur (reduce assert-black jg (concat @bad-strokes-deterministic @bad-nodes)))
          ;; if we have a non-deterministic bad stroke, employ the strategy
          (not-empty @bad-strokes-nondeterministic)
          (recur (assert-black jg (abduce-strategy jg @bad-strokes-nondeterministic)))
          :else
          (do (when @debugging? (println "Axioms failed in spread-abduce.\n\n"))
              jg))))))

(defn spread-black-bad-strokes
  "Bad stroke w.r.t. black: A stroke is white but has all incoming black nodes."
  [jg]
  (filter (fn [s] (and (white? jg s)
                       (and (not-empty (jgin jg s))
                            (every? (fn [n] (black? jg n))
                                    (jgin jg s)))))
          (strokes jg)))

(defn spread-black-bad-nodes
  "Bad node w.r.t. black: A node is white but has some incoming black stroke."
  [jg]
  (filter (fn [n] (and (white? jg n)
                       (some (fn [s] (black? jg s)) (jgin jg n))))
          (nodes jg)))

(defn spread-black
  [jg]
  (loop [jg jg]
    (if (check-color-axioms jg)
      ;; nothing to do, everything checks out
      (do (when @debugging? (println "All axioms satisfied in spread-black.\n\n"))
          jg)
      ;; something to do (inconsistent), spread black.
      (let [bad-strokes (spread-black-bad-strokes jg)
            bad-nodes (spread-black-bad-nodes jg)]
        (when @debugging?
          (println "Spreading black.")
          (println "Found bad strokes:" bad-strokes)
          (println "Found bad nodes:" bad-nodes))
        (if (or (not-empty bad-strokes) (not-empty bad-nodes))
          (let [to-assert-black (concat bad-strokes bad-nodes)]
            (recur (reduce assert-black jg to-assert-black)))
          (do (when @debugging? (println "Axioms failed in spread-black.\n\n"))
              jg))))))

(defn contract
  "Only colors white (upwards and downwards). A \"strategy\" is needed. Uses white-strategy for now."
  [jg nodes & {:keys [white-strategy]
               :or {white-strategy spread-white-default-strategy}}]
  (assert (sequential? nodes))
  (when @debugging? (println "Contracting by" nodes))
  (let [jg-asserted (reduce assert-white jg nodes)
        jg-whitened (spread-white jg-asserted white-strategy)]
    ;; if it didn't work out (no way to spread-white consistently), return nil
    (if (check-color-axioms jg-whitened)
      jg-whitened
      nil)))

(defn abduce
  "Only colors black (upwards and downwards). A \"strategy\" is needed."
  [jg nodes & {:keys [abduce-strategy white-strategy]
               :or {abduce-strategy spread-abduce-default-strategy
                    white-strategy spread-white-default-strategy}}]
  (assert (sequential? nodes))
  (let [jg-asserted (reduce assert-black jg nodes)
        jg-asserted-initial (reduce assert-black-initial jg-asserted (filter #(initial? jg-asserted %) nodes))
        jg-blackened (spread-abduce jg-asserted-initial abduce-strategy)]
    ;; if it didn't work out (no way to spread-black consistently), return nil
    (cond
      (check-color-axioms jg-blackened)
      jg-blackened
      (black? jg-blackened :bottom)
      (contract jg-blackened [:bottom] :white-strategy white-strategy)
      :else
      nil)))

(defn expand
  "Only colors black, and only downwards. 'bottom' node may be colored black (which is inconsistent)."
  [jg nodes]
  (assert (sequential? nodes))
  (let [jg-asserted (reduce assert-black jg nodes)
        jg-asserted-initial (reduce assert-black-initial jg (filter #(initial? jg %) nodes))]
    (spread-black jg-asserted-initial)))

(defn revise
  "Only colors black, and only downwards, except when 'bottom' is colored black.
  A white-strategy is needed in case 'bottom' is turned black and contraction is required."
  [jg nodes & {:keys [white-strategy]
               :or {white-strategy spread-white-default-strategy}}]
  (let [jg-blackened (expand jg nodes)]
    (cond
      (check-color-axioms jg-blackened)
      jg-blackened
      (black? jg-blackened :bottom)
      (contract jg-blackened [:bottom] :white-strategy white-strategy)
      :else
      nil)))
