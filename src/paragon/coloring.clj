(ns paragon.coloring
  (:require [paragon.core :refer :all]
            [paragon.axioms :refer :all]
            [paragon.strategies :refer :all]
            [paragon.visualization :as visualization]))

(defn assert-color
  [fdn stroke-or-node color]
  (when @debugging? (println "asserting" stroke-or-node "as" color))
  (let [fdn-colored (assoc-in fdn [:coloring stroke-or-node] color)]
    (if (node? fdn-colored stroke-or-node)
      (update-priority fdn-colored stroke-or-node)
      fdn-colored)))

(defn assert-black
  [fdn stroke-or-node]
  (assert-color fdn stroke-or-node :black))

(defn assert-black-initial
  [fdn node]
  (-> fdn (assert-black node) (assert-black (format ".%s" (fdnstr node)))))

(defn assert-white
  [fdn stroke-or-node]
  (assert-color fdn stroke-or-node :white))


(defn white-bad-strokes
  "Bad stroke w.r.t. white: A stroke (#i) is black but points a white
  node (#j) and i <= j; or a stroke (#j) is black but some white
  node (#i) points to it, and j <= i."
  [fdn]
  (filter (fn [s]
            (let [spriority (fdnpriority fdn s)
                  obspriority (observed-priority fdn s)
                  n (first (fdnout fdn s)) ;; this stroke's out node
                  npriority (fdnpriority fdn n)]
              (and (black? fdn s)
                   (or (and (white? fdn n)
                            (or (< spriority npriority)
                                (<= obspriority (observed-priority fdn n))))
                       (some (fn [n2] (and (white? fdn n2)
                                           (or (<= spriority (fdnpriority fdn n2))
                                               (<= obspriority (observed-priority fdn n2)))))
                             (fdnin fdn s))))))
          (strokes fdn)))

(defn white-bad-nodes-deterministic
  "TODO: update.

  Bad node w.r.t. white (deterministic): A node (#j) is black but all
  of its incoming strokes are white and all strokes have priority (#i)
  such that j <= i."
  [fdn]
  #_(doseq [n (nodes fdn)]
      (prn n (fdnpriority fdn n) (observed-priority fdn n)
           (map (fn [s] [s (fdnpriority fdn s) (observed-priority fdn s)])
                (fdnin fdn n))))
  (filter (fn [n]
            (let [npriority (fdnpriority fdn n)
                  obnpriority (observed-priority fdn n)
                  ins (fdnin fdn n)]
              (and (black? fdn n)
                   (every? (fn [s] (white? fdn s)) ins)
                   (or (every? (fn [s] (< npriority (fdnpriority fdn s))) ins)
                       (every? (fn [s] (<= obnpriority (observed-priority fdn s))) ins)))))
          (nodes fdn)))

(defn white-bad-nodes-nondeterministic
  "Bad node w.r.t. white (non-deterministic): A node (#i) is black but
  points to a white stroke (#j) that has only black nodes pointing to
  it, and j >= i. One of these black nodes must turn white."
  [fdn]
  (filter (fn [n]
            (let [npriority (fdnpriority fdn n)]
              (and (black? fdn n)
                   (some (fn [s] (and (white? fdn s)
                                      (<= npriority (fdnpriority fdn s))
                                      (every? (fn [n2] (black? fdn n2)) (fdnin fdn s))))
                         (fdnout fdn n)))))
          (nodes fdn)))

(defn spread-white
  [fdn white-strategy]
  (loop [fdn fdn]
    (if (check-color-axioms fdn)
      ;; nothing to do, everything checks out
      (do (when @debugging? (println "All axioms satisfied in spread-white.\n\n"))
          fdn)
      ;; something to do (inconsistent), spread white
      (let [bad-strokes (delay (white-bad-strokes fdn))
            bad-nodes-deterministic (delay (white-bad-nodes-deterministic fdn))
            bad-nodes-nondeterministic (delay (white-bad-nodes-nondeterministic fdn))]
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
          (let [choice (white-strategy fdn @bad-nodes-nondeterministic)]
            (recur (assert-white fdn choice)))
          :else
          (do (when @debugging? (println "Axioms failed in spread-white."))
              fdn))))))

(defn abduce-bad-strokes-deterministic
  "Bad stroke w.r.t. abduction (deterministic): A stroke (#j) is white
  but all its incoming nodes are black and have priority (#i) such
  that j <= i."
  [fdn]
  (filter (fn [s]
            (let [spriority (fdnpriority fdn s)
                  ns (fdnin fdn s)]
              (and (white? fdn s)
                   (and (not-empty ns)
                        (every? (fn [n] (and (black? fdn n)
                                             (<= spriority (fdnpriority fdn n))))
                                ns)))))
          (strokes fdn)))

(defn abduce-bad-strokes-nondeterministic
  "Bad stroke w.r.t. abduction (non-deterministic): A stroke (#i) is
  white but points to a black node (#j) that has only white strokes
  pointing to it, and j >= i."
  [fdn]
  (filter (fn [s]
            (let [spriority (fdnpriority fdn s)
                  obspriority (observed-priority fdn s)
                  n (first (fdnout fdn s))
                  npriority (fdnpriority fdn n)]
              (and (white? fdn s)
                   (black? fdn n)
                   (or (< spriority npriority)
                       (<= obspriority (observed-priority fdn n)))
                   (every? (fn [s2] (white? fdn s2))
                           (fdnin fdn n)))))
          (strokes fdn)))

(defn abduce-bad-nodes
  "Bad node w.r.t. abduction: A node (#i) is white but is pointed to
  by a black stroke (#j) or points to a black stroke (#j), and j >=
  i."
  [fdn]
  (filter (fn [n]
            (let [npriority (fdnpriority fdn n)]
              (and (white? fdn n)
                   (or (some (fn [s] (and (black? fdn s)
                                          (>= (fdnpriority fdn s) npriority)))
                             (fdnin fdn n))
                       (some (fn [s] (and (black? fdn s)
                                          (>= (fdnpriority fdn s) npriority)))
                             (fdnout fdn n))))))
          (nodes fdn)))

(defn spread-abduce
  [fdn abduce-strategy]
  (loop [fdn fdn]
    (if (check-color-axioms fdn)
      ;; nothing to do, everything checks out
      (do (when @debugging? (println "All axioms satisfied in spread-abduce.\n\n"))
          fdn)
      ;; something to do (inconsistent), spread abductively
      (let [bad-strokes-deterministic (delay (abduce-bad-strokes-deterministic fdn))
            bad-strokes-nondeterministic (delay (abduce-bad-strokes-nondeterministic fdn))
            bad-nodes (delay (abduce-bad-nodes fdn))]
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

(defn black-bad-strokes
  "Bad stroke w.r.t. black: A stroke (#i) is white but has all
  incoming black nodes, and some black node's priority (#j) is such
  that j >= i."
  [fdn]
  (filter (fn [s]
            (let [spriority (fdnpriority fdn s)
                  ns (fdnin fdn s)]
              (and (white? fdn s)
                   (and (not-empty ns)
                        (every? (fn [n] (black? fdn n)) ns)
                        (some (fn [n] (>= (fdnpriority fdn n) spriority)) ns)))))
          (strokes fdn)))

(defn black-bad-nodes
  "Bad node w.r.t. black: A node (#i) is white but has some incoming
  black stroke (#j), and j >= i."
  [fdn]
  (filter (fn [n]
            (let [npriority (fdnpriority fdn n)]
              (and (white? fdn n)
                   (some (fn [s] (and (black? fdn s)
                                      (>= (fdnpriority fdn s) npriority)))
                         (fdnin fdn n)))))
          (nodes fdn)))

(defn spread-black
  [fdn]
  (loop [fdn fdn]
    (if (check-color-axioms fdn)
      ;; nothing to do, everything checks out
      (do (when @debugging? (println "All axioms satisfied in spread-black.\n\n"))
          fdn)
      ;; something to do (inconsistent), spread black.
      (let [bad-strokes (black-bad-strokes fdn)
            bad-nodes (black-bad-nodes fdn)]
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
  "Only colors black, and only downwards. May result in an FDN that
  does not satisfy color axioms. Use revise/abduce instead."
  [fdn nodes & {:keys [inc-priorities?]
                :or {inc-priorities? true}}]
  (assert (sequential? nodes))
  (assert fdn)
  (let [fdn-priority (if inc-priorities?
                       (inc-priority-counter fdn)
                       fdn)
        fdn-asserted-non-initial (reduce assert-black fdn-priority
                                         (filter #(not (initial? fdn-priority %)) nodes))
        fdn-asserted-initial (reduce assert-black-initial fdn-asserted-non-initial
                                     (filter #(initial? fdn-asserted-non-initial %) nodes))]
    (spread-black fdn-asserted-initial)))

(defn contract
  "Colors white (upwards and downwards), and abduces black if color
  axioms are not satisfied. A contraction and abduction \"strategy\"
  may be provided."
  [fdn nodes & {:keys [white-strategy abduce-strategy inc-priorities? abduce?]
                :or {white-strategy spread-white-default-strategy
                     abduce-strategy spread-abduce-default-strategy
                     inc-priorities? true
                     abduce? true}}]
  (assert (sequential? nodes))
  (assert fdn)
  (when @debugging? (println "Contracting by" nodes))
  (let [fdn-priority (if inc-priorities?
                       (inc-priority-counter fdn)
                       fdn)
        fdn-observed (reduce observe fdn-priority nodes)
        fdn-asserted (reduce assert-white fdn-observed nodes)
        fdn-whitened (spread-white fdn-asserted white-strategy)]
    (cond (check-color-axioms fdn-whitened)
          fdn-whitened
          abduce?
          (let [fdn-abduced (spread-abduce fdn-whitened abduce-strategy)]
            (if (check-color-axioms fdn-abduced)
              fdn-abduced
              (spread-white fdn-abduced white-strategy)))
          :else
          nil)))

(defn revise
  "Only colors black, and only downwards, except when 'bottom' is colored black.
  A white-strategy is needed in case 'bottom' is turned black and
  contraction is required."
  [fdn nodes & {:keys [white-strategy inc-priorities?]
                :or {white-strategy spread-white-default-strategy
                     inc-priorities? true}}]
  (assert fdn)
  (let [fdn-blackened (expand fdn nodes :inc-priorities? inc-priorities?)]
    (cond
      (check-color-axioms fdn-blackened)
      fdn-blackened
      (some #(black? fdn-blackened %)
            (fdnin fdn-blackened :bottom))
      (contract fdn-blackened [:bottom] :white-strategy white-strategy :inc-priorities? false)
      :else
      nil)))

(defn abduce
  "Only colors black (upwards and downwards). An abduction and
  contraction \"strategy\" are needed."
  [fdn nodes & {:keys [abduce-strategy white-strategy inc-priorities?]
               :or {abduce-strategy spread-abduce-default-strategy
                    white-strategy spread-white-default-strategy
                    inc-priorities? true}}]
  (assert (sequential? nodes))
  (assert fdn)
  (let [fdn-priority (if inc-priorities?
                       (inc-priority-counter fdn)
                       fdn)
        fdn-observed (reduce observe fdn-priority nodes)
        fdn-asserted-non-initial (reduce assert-black fdn-observed
                                         (filter #(not (initial? fdn-observed %)) nodes))
        fdn-asserted-initial (reduce assert-black-initial fdn-asserted-non-initial
                                     (filter #(initial? fdn-asserted-non-initial %) nodes))
        fdn-blackened (spread-abduce fdn-asserted-initial abduce-strategy)]
    (cond
      (check-color-axioms fdn-blackened)
      fdn-blackened
      :else
      (let [fdn-whitened (spread-white fdn-blackened white-strategy)]
        (if (check-color-axioms fdn-whitened)
          fdn-whitened
          (spread-abduce fdn-whitened abduce-strategy))))))

