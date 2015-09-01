(ns paragon.coloring
  (:require [paragon.core :refer :all]
            [paragon.axioms :refer :all]
            [paragon.strategies :refer :all]))

(defn assert-color
  [fdn stroke-or-node color]
  (when @debugging? (println "asserting" stroke-or-node "as" color))
  (assoc-in fdn [:coloring stroke-or-node] color))

(defn assert-black
  [fdn stroke-or-node]
  (assert-color fdn stroke-or-node :black))

(defn assert-black-initial
  [fdn node]
  (-> fdn (assert-black node) (assert-black (format ".%s" (fdnstr node)))))

(defn assert-white
  [fdn stroke-or-node]
  (assert-color fdn stroke-or-node :white))


(defn spread-white-bad-strokes
  "Bad stroke w.r.t. white: A stroke is black but points a white node, or
  a stroke is black but some white node points to it."
  [fdn]
  (filter (fn [s] (and (black? fdn s)
                       (or (white? fdn (first (fdnout fdn s)))
                           (some (fn [n] (white? fdn n)) (fdnin fdn s)))))
          (strokes fdn)))

(defn spread-white-bad-nodes-deterministic
  "Bad node w.r.t. white (deterministic): A node is black but all of its incoming strokes are white."
  [fdn]
  (filter (fn [n] (and (black? fdn n)
                       (every? (fn [s] (white? fdn s)) (fdnin fdn n))))
          (nodes fdn)))

(defn spread-white-bad-nodes-nondeterministic
  "Bad node w.r.t. white (non-deterministic): A node is black but points to a white stroke that
  has only black nodes pointing to it."
  [fdn]
  (filter (fn [n] (and (black? fdn n)
                       (some (fn [s] (and (white? fdn s)
                                          (every? (fn [n2] (black? fdn n2)) (fdnin fdn s))))
                             (fdnout fdn n))))
          (nodes fdn)))

(defn spread-white
  [fdn white-strategy]
  (loop [fdn fdn]
    (if (check-color-axioms fdn)
      ;; nothing to do, everything checks out
      (do (when @debugging? (println "All axioms satisfied in spread-white.\n\n"))
          fdn)
      ;; something to do (inconsistent), spread white
      (let [bad-strokes (delay (spread-white-bad-strokes fdn))
            bad-nodes-deterministic (delay (spread-white-bad-nodes-deterministic fdn))
            bad-nodes-nondeterministic (delay (spread-white-bad-nodes-nondeterministic fdn))]
        (when @debugging?
          (println "Spreading white.")
          (println "Found bad strokes:" @bad-strokes)
          (println "Found bad nodes (deterministic):" @bad-nodes-deterministic)
          (println "Found bad nodes (non-deterministic):" @bad-nodes-nondeterministic))
        (cond
          ;; if we have bad strokes, just take care of them; no need for strategy
          ;; or, if we have deterministic bad nodes, just take care of them; no need for strategy
          (or (not-empty @bad-strokes) (not-empty @bad-nodes-deterministic))
          (recur (reduce assert-white fdn (concat @bad-strokes @bad-nodes-deterministic)))
          ;; if we have a non-deterministic bad node, employ the strategy
          (not-empty @bad-nodes-nondeterministic)
          (recur (assert-white fdn (white-strategy fdn @bad-nodes-nondeterministic)))
          :else
          (do (when @debugging? (println "Axioms failed in spread-white."))
              fdn))))))

(defn spread-abduce-bad-strokes-deterministic
  "Bad stroke w.r.t. abduction (deterministic): A stroke is white but all its incoming nodes are black."
  [fdn]
  (filter (fn [s] (and (white? fdn s)
                       (and (not-empty (fdnin fdn s))
                            (every? (fn [n] (black? fdn n))
                                    (fdnin fdn s)))))
          (strokes fdn)))

(defn spread-abduce-bad-strokes-nondeterministic
  "Bad stroke w.r.t. abduction (non-deterministic): A stroke is white but points to a black node that
  has only white strokes pointing to it."
  [fdn]
  (filter (fn [s] (and (white? fdn s)
                       (black? fdn (first (fdnout fdn s)))
                       (every? (fn [s2] (white? fdn s2))
                               (fdnin fdn (first (fdnout fdn s))))))
          (strokes fdn)))

(defn spread-abduce-bad-nodes
  "Bad node w.r.t. abduction: A node is white but is pointed to by a black stroke or points to a black stroke."
  [fdn]
  (filter (fn [n] (and (white? fdn n)
                       (or (some (fn [s] (black? fdn s)) (fdnin fdn n))
                           (some (fn [s] (black? fdn s)) (fdnout fdn n)))))
          (nodes fdn)))

(defn spread-abduce
  [fdn abduce-strategy]
  (loop [fdn fdn]
    (if (check-color-axioms fdn)
      ;; nothing to do, everything checks out
      (do (when @debugging? (println "All axioms satisfied in spread-abduce.\n\n"))
          fdn)
      ;; something to do (inconsistent), spread abductively
      (let [bad-strokes-deterministic (delay (spread-abduce-bad-strokes-deterministic fdn))
            bad-strokes-nondeterministic (delay (spread-abduce-bad-strokes-nondeterministic fdn))
            bad-nodes (delay (spread-abduce-bad-nodes fdn))]
        (when @debugging?
          (println "Spreading abductively.")
          (println "Found bad strokes (deterministic):" @bad-strokes-deterministic)
          (println "Found bad strokes (non-deterministic):" @bad-strokes-nondeterministic)
          (println "Found bad nodes:" @bad-nodes))
        (cond
          ;; if we have deterministic bad strokes and/or nodes, just take care of them; no need for strategy
          (or (not-empty @bad-strokes-deterministic) (not-empty @bad-nodes))
          (recur (reduce assert-black fdn (concat @bad-strokes-deterministic @bad-nodes)))
          ;; if we have a non-deterministic bad stroke, employ the strategy
          (not-empty @bad-strokes-nondeterministic)
          (recur (assert-black fdn (abduce-strategy fdn @bad-strokes-nondeterministic)))
          :else
          (do (when @debugging? (println "Axioms failed in spread-abduce.\n\n"))
              fdn))))))

(defn spread-black-bad-strokes
  "Bad stroke w.r.t. black: A stroke is white but has all incoming black nodes."
  [fdn]
  (filter (fn [s] (and (white? fdn s)
                       (and (not-empty (fdnin fdn s))
                            (every? (fn [n] (black? fdn n))
                                    (fdnin fdn s)))))
          (strokes fdn)))

(defn spread-black-bad-nodes
  "Bad node w.r.t. black: A node is white but has some incoming black stroke."
  [fdn]
  (filter (fn [n] (and (white? fdn n)
                       (some (fn [s] (black? fdn s)) (fdnin fdn n))))
          (nodes fdn)))

(defn spread-black
  [fdn]
  (loop [fdn fdn]
    (if (check-color-axioms fdn)
      ;; nothing to do, everything checks out
      (do (when @debugging? (println "All axioms satisfied in spread-black.\n\n"))
          fdn)
      ;; something to do (inconsistent), spread black.
      (let [bad-strokes (spread-black-bad-strokes fdn)
            bad-nodes (spread-black-bad-nodes fdn)]
        (when @debugging?
          (println "Spreading black.")
          (println "Found bad strokes:" bad-strokes)
          (println "Found bad nodes:" bad-nodes))
        (if (or (not-empty bad-strokes) (not-empty bad-nodes))
          (let [to-assert-black (concat bad-strokes bad-nodes)]
            (recur (reduce assert-black fdn to-assert-black)))
          (do (when @debugging? (println "Axioms failed in spread-black.\n\n"))
              fdn))))))

(defn expand
  "Only colors black, and only downwards. 'bottom' node may be colored black (which is inconsistent)."
  [fdn nodes]
  (assert (sequential? nodes))
  (let [fdn-asserted (reduce assert-black fdn nodes)
        fdn-asserted-initial (reduce assert-black-initial fdn (filter #(initial? fdn %) nodes))]
    (spread-black fdn-asserted-initial)))

(defn contract
  "Only colors white (upwards and downwards). A \"strategy\" is needed. Uses white-strategy for now."
  [fdn nodes & {:keys [white-strategy]
               :or {white-strategy spread-white-default-strategy}}]
  (assert (sequential? nodes))
  (when @debugging? (println "Contracting by" nodes))
  (let [fdn-asserted (reduce assert-white fdn nodes)
        fdn-whitened (spread-white fdn-asserted white-strategy)]
    ;; if it didn't work out (no way to spread-white consistently), return nil
    (if (check-color-axioms fdn-whitened)
      fdn-whitened
      nil)))

(defn revise
  "Only colors black, and only downwards, except when 'bottom' is colored black.
  A white-strategy is needed in case 'bottom' is turned black and contraction is required."
  [fdn nodes & {:keys [white-strategy]
               :or {white-strategy spread-white-default-strategy}}]
  (let [fdn-blackened (expand fdn nodes)]
    (cond
      (check-color-axioms fdn-blackened)
      fdn-blackened
      (black? fdn-blackened :bottom)
      (contract fdn-blackened [:bottom] :white-strategy white-strategy)
      :else
      nil)))

(defn abduce
  "Only colors black (upwards and downwards). A \"strategy\" is needed."
  [fdn nodes & {:keys [abduce-strategy white-strategy]
               :or {abduce-strategy spread-abduce-default-strategy
                    white-strategy spread-white-default-strategy}}]
  (assert (sequential? nodes))
  (let [fdn-asserted (reduce assert-black fdn nodes)
        fdn-asserted-initial (reduce assert-black-initial fdn-asserted (filter #(initial? fdn-asserted %) nodes))
        fdn-blackened (spread-abduce fdn-asserted-initial abduce-strategy)]
    ;; if it didn't work out (no way to spread-black consistently), return nil
    (cond
      (check-color-axioms fdn-blackened)
      fdn-blackened
      (black? fdn-blackened :bottom)
      (contract fdn-blackened [:bottom] :white-strategy white-strategy)
      :else
      nil)))

