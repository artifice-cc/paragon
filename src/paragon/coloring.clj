(ns paragon.coloring
  (:require [clojure.set :as set])
  (:require [paragon.core :refer :all]
            [paragon.axioms :refer :all]
            [paragon.strategies :refer :all]
            [paragon.visualization :as visualization]))

(defn assert-color
  [fdn stroke-or-node color]
  (info "asserting" stroke-or-node "as" color)
  (-> fdn
      (assoc-in [:coloring stroke-or-node] color)
      (update-priority stroke-or-node)))

(defn assert-black
  [fdn stroke-or-node]
  (assert-color fdn stroke-or-node :black))

(defn assert-black-initial
  [fdn node]
  (-> fdn
      (assert-black node)
      (assert-black (format ".%s" (fdnstr node)))))

(defn assert-white
  [fdn stroke-or-node]
  (assert-color fdn stroke-or-node :white))

(defn white-bad-strokes
  "Bad stroke w.r.t. white: A stroke (#i) is black but points a white
  node (#j) and i <= j; or a stroke (#j) is black but some white
  node (#i) points to it, and j <= i."
  [fdn]
  (filter (fn [s]
            ;; n is this stroke's single out node
            (let [n (first (fdnout fdn s))]
              (and (black? fdn s)
                   (or (white? fdn n)
                       (some (fn [n2] (white? fdn n2)) (fdnin fdn s))))))
          (sort-by fdnstr (strokes fdn))))

(defn white-bad-nodes-deterministic
  "TODO: update.

  Bad node w.r.t. white (deterministic): A node (#j) is black but all
  of its incoming strokes are white and all strokes have priority (#i)
  such that j <= i."
  [fdn]
  (doall (filter (fn [n]
                   (let [ins (fdnin fdn n)
                         priority (fdnpriority fdn n)
                         min-in-priority (apply min (map (partial fdnpriority fdn) ins))
                         bad? (and (black? fdn n)
                                   (every? (fn [s] (white? fdn s)) ins)
                                   (<= priority min-in-priority))]
                     (when (black? fdn n)
                       (trace
                        (format "spread-white: Considering node %s (priority %d, min-in-priority %d)"
                                n priority min-in-priority)))
                     bad?))
                 (sort-by fdnstr (nodes fdn)))))

(defn white-bad-nodes-nondeterministic
  "Bad node w.r.t. white (non-deterministic): A node (#i) is black but
  points to a white stroke (#j) that has only black nodes pointing to
  it, and j >= i. One of these black nodes must turn white."
  [fdn]
  (filter (fn [n]
            (and (black? fdn n)
                 (some (fn [s] (and (white? fdn s)
                                    (every? (fn [n2] (black? fdn n2)) (fdnin fdn s))))
                       (fdnout fdn n))))
          (sort-by fdnstr (nodes fdn))))

(defn spread-white
  [fdn white-strategy]
  (loop [fdn fdn]
    (if (check-color-axioms fdn)
      ;; nothing to do, everything checks out
      (do (success "\n+++ All axioms satisfied in spread-white.\n\n")
          fdn)
      ;; something to do (inconsistent), spread white
      (let [bad-strokes (delay (white-bad-strokes fdn))
            bad-nodes-deterministic (delay (white-bad-nodes-deterministic fdn))
            bad-nodes-nondeterministic (delay (white-bad-nodes-nondeterministic fdn))]
        (info "\n--- Spreading white.")
        (info "Found bad strokes:" @bad-strokes)
        (info "Found bad nodes (deterministic):" @bad-nodes-deterministic)
        (info "Found bad nodes (non-deterministic):" @bad-nodes-nondeterministic)
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
          (do (error "\n!!! Axioms failed in spread-white.")
              fdn))))))

(defn abduce-bad-strokes-deterministic
  "Bad stroke w.r.t. abduction (deterministic): A stroke (#j) is white
  but all its incoming nodes are black and have priority (#i) such
  that j <= i."
  [fdn]
  (filter (fn [s]
            (let [ns (fdnin fdn s)]
              (and (white? fdn s)
                   (and (not-empty ns)
                        (every? (fn [n] (black? fdn n)) ns)))))
          (sort-by fdnstr (strokes fdn))))

(defn abduce-bad-strokes-nondeterministic
  "Bad stroke w.r.t. abduction (non-deterministic): A stroke (#i) is
  white but points to a black node (#j) that has only white strokes
  pointing to it, and j >= i."
  [fdn]
  (doall (filter (fn [s]
                   ;; n is this stroke's single out node
                   (let [n (first (fdnout fdn s))
                         priority (fdnpriority fdn s)
                         out-priority (fdnpriority fdn n)
                         bad? (and (white? fdn s)
                                   (black? fdn n)
                                   (every? (fn [s2] (white? fdn s2)) (fdnin fdn n))
                                   (<= priority out-priority))]
                     (when (white? fdn s)
                       (trace (format "spread-abduce: Considering stroke %s (priority %d, out-priority %d)"
                                      s priority out-priority)))
                     bad?))
                 (sort-by fdnstr (strokes fdn)))))

(defn abduce-bad-nodes
  "Bad node w.r.t. abduction: A node (#i) is white but is pointed to
  by a black stroke (#j) or points to a black stroke (#j), and j >=
  i."
  [fdn]
  (filter (fn [n]
            (and (not= :bottom n)
                 (white? fdn n)
                 (or (some (fn [s] (black? fdn s))
                           (fdnin fdn n))
                     (some (fn [s] (black? fdn s))
                           (fdnout fdn n)))))
          (sort-by fdnstr (nodes fdn))))

(defn spread-abduce
  [fdn abduce-strategy]
  (loop [fdn fdn]
    (if (check-color-axioms fdn)
      ;; nothing to do, everything checks out
      (do (success "\n+++ All axioms satisfied in spread-abduce.\n\n")
          fdn)
      ;; something to do (inconsistent), spread abductively
      (let [bad-strokes-deterministic (delay (abduce-bad-strokes-deterministic fdn))
            bad-strokes-nondeterministic (delay (abduce-bad-strokes-nondeterministic fdn))
            bad-nodes (delay (abduce-bad-nodes fdn))]
        (when @debugging?
          (info "\n--- Spreading abductively.")
          (info "Found bad strokes (deterministic):" @bad-strokes-deterministic)
          (info "Found bad strokes (non-deterministic):" @bad-strokes-nondeterministic)
          (info "Found bad nodes:" @bad-nodes))
        (cond
          ;; if we have deterministic bad strokes and/or nodes, just take care of them; no need for strategy
          (or (not-empty @bad-strokes-deterministic) (not-empty @bad-nodes))
          (recur (reduce assert-black fdn (concat @bad-strokes-deterministic @bad-nodes)))
          ;; if we have a non-deterministic bad stroke, employ the strategy
          (not-empty @bad-strokes-nondeterministic)
          (let [choice (abduce-strategy fdn @bad-strokes-nondeterministic)]
            (recur (assert-black fdn choice)))
          :else
          (do (error "\n!!! Axioms failed in spread-abduce.\n\n")
              fdn))))))

(defn black-bad-strokes
  "Bad stroke w.r.t. black: A stroke (#i) is white but has all
  incoming black nodes, and some black node's priority (#j) is such
  that j >= i."
  [fdn]
  (filter (fn [s]
            (let [ns (fdnin fdn s)]
              (and (white? fdn s)
                   (and (not-empty ns)
                        (every? (fn [n] (black? fdn n)) ns)))))
          (sort-by fdnstr (strokes fdn))))

(defn black-bad-nodes
  "Bad node w.r.t. black: A node (#i) is white but has some incoming
  black stroke (#j), and j >= i."
  [fdn]
  (filter (fn [n]
            (and (white? fdn n)
                 (some (fn [s] (black? fdn s)) (fdnin fdn n))))
          (sort-by fdnstr (nodes fdn))))

(defn spread-black
  [fdn]
  (loop [fdn fdn]
    (if (check-color-axioms fdn)
      ;; nothing to do, everything checks out
      (do (success "\n+++ All axioms satisfied in spread-black.\n\n")
          fdn)
      ;; something to do (inconsistent), spread black.
      (let [bad-strokes (black-bad-strokes fdn)
            bad-nodes (black-bad-nodes fdn)]
        (info "\n--- Spreading black.")
        (info "Found bad strokes:" bad-strokes)
        (info "Found bad nodes:" bad-nodes)
        (if (or (not-empty bad-strokes) (not-empty bad-nodes))
          (let [to-assert-black (concat bad-strokes bad-nodes)]
            (recur (reduce assert-black fdn to-assert-black)))
          (do (error "\n!!! Axioms failed in spread-black.\n\n")
              fdn))))))

(defn expand
  "Only colors black, and only downwards. May result in an FDN that
  does not satisfy color axioms. Use revise/abduce instead."
  [fdn nodes]
  (assert (sequential? nodes))
  (assert fdn)
  (status "\n\n*** Expanding by" nodes)
  (let [fdn-priority (inc-priority-counter fdn)
        fdn-asserted-non-initial (reduce assert-black fdn-priority
                                         (filter #(not (initial? fdn-priority %)) nodes))
        fdn-asserted-initial (reduce assert-black-initial fdn-asserted-non-initial
                                     (filter #(initial? fdn-asserted-non-initial %) nodes))]
    (spread-black fdn-asserted-initial)))

(defn contract
  "Colors white (upwards and downwards), and abduces black if color
  axioms are not satisfied. A contraction and abduction \"strategy\"
  may be provided."
  [fdn nodes & {:keys [white-strategy abduce-strategy abduce?]
                :or {white-strategy spread-white-default-strategy
                     abduce-strategy spread-abduce-default-strategy
                     abduce? true}}]
  (assert (sequential? nodes))
  (assert fdn)
  (status "\n\n*** Contracting by" nodes)
  (let [fdn-priority (inc-priority-counter fdn)
        fdn-asserted (reduce assert-white fdn-priority nodes)]
    (loop [fdn-colored (spread-white fdn-asserted white-strategy)
           last-spread :white]
      (if (check-color-axioms fdn-colored)
        fdn-colored
        (let [new-spread (if (= last-spread :abduce) :white :abduce)
              new-fdn (if (= new-spread :abduce)
                        (spread-abduce fdn-colored abduce-strategy)
                        (spread-white fdn-colored white-strategy))]
          (recur new-fdn new-spread))))))

(defn revise
  "Only colors black, and only downwards, except when 'bottom' is colored black.
  A white-strategy is needed in case 'bottom' is turned black and
  contraction is required."
  [fdn nodes & {:keys [white-strategy]
                :or {white-strategy spread-white-default-strategy}}]
  (assert fdn)
  (status "\n\n*** Revising by" nodes)
  (let [fdn-blackened (expand fdn nodes)]
    (cond
      (check-color-axioms fdn-blackened)
      fdn-blackened
      (some #(black? fdn-blackened %)
            (fdnin fdn-blackened :bottom))
      (contract fdn-blackened [:bottom] :white-strategy white-strategy)
      :else
      nil)))

(defn abduce
  "Only colors black (upwards and downwards). An abduction and
  contraction \"strategy\" are needed."
  [fdn nodes & {:keys [abduce-strategy white-strategy]
               :or {abduce-strategy spread-abduce-default-strategy
                    white-strategy spread-white-default-strategy}}]
  (assert (sequential? nodes))
  (assert fdn)
  (status "\n\n*** Abducing by" nodes)
  (let [fdn-priority (inc-priority-counter fdn)
        fdn-asserted-non-initial (reduce assert-black fdn-priority
                                         (filter #(not (initial? fdn-priority %)) nodes))
        fdn-asserted-initial (reduce assert-black-initial fdn-asserted-non-initial
                                     (filter #(initial? fdn-asserted-non-initial %) nodes))]
    (loop [fdn-colored (spread-abduce fdn-asserted-initial abduce-strategy)
           last-spread :abduce]
      (if (check-color-axioms fdn-colored)
        fdn-colored
        (let [new-spread (if (= last-spread :abduce) :white :abduce)
              new-fdn (if (= new-spread :abduce)
                        (spread-abduce fdn-colored abduce-strategy)
                        (spread-white fdn-colored white-strategy))]
          (recur new-fdn new-spread))))))

