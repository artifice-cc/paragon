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
            (let [priority (fdnpriority fdn s)
                  n (first (fdnout fdn s)) ;; n is this stroke's single out node
                  ins (fdnin fdn s)]
              (and (black? fdn s)
                   (or (and (white? fdn n)
                            (<= priority (fdnpriority fdn n)))
                       (and (not-empty ins)
                            (some (fn [n2]
                                    (and (white? fdn n2)
                                         (<= priority (fdnpriority fdn n2))))
                                  ins))))))
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
                         bad? (and (black? fdn n)
                                   (every? (fn [s]
                                             (and (white? fdn s)
                                                  (<= priority (fdnpriority fdn s))))
                                           ins))]
                     (when (black? fdn n)
                       (trace
                        (format "spread-white: Considering node %s (priority %d)" n priority)))
                     bad?))
                 (sort-by fdnstr (nodes fdn)))))

(defn white-bad-nodes-nondeterministic
  "Bad node w.r.t. white (non-deterministic): A node (#i) is black but
  points to a white stroke (#j) that has only black nodes pointing to
  it, and j >= i. One of these black nodes must turn white."
  [fdn]
  (filter (fn [n]
            (let [priority (fdnpriority fdn n)
                  outs (fdnout fdn n)]
              (when (black? fdn n)
                (trace
                 (format "spread-white: Considering node %s (priority %d)" n priority)))
              (and (black? fdn n)
                   (some (fn [s]
                           (trace
                            (format "spread-white: Considering node %s (priority %d), stroke %s (priority %s)"
                                    n priority s (fdnpriority fdn s)))
                           (and (white? fdn s)
                                (every? (fn [n2] (black? fdn n2)) (fdnin fdn s))
                                (<= priority (fdnpriority fdn s))))
                         outs))))
          (sort-by fdnstr (nodes fdn))))

(defn abduce-bad-strokes-deterministic
  "Bad stroke w.r.t. abduction (deterministic): A stroke (#j) is white
  but all its incoming nodes are black and have priority (#i) such
  that j <= i."
  [fdn]
  (filter (fn [s]
            (let [priority (fdnpriority fdn s)
                  ins (fdnin fdn s)]
              (and (white? fdn s)
                   (and (not-empty ins)
                        (every? (fn [n] (and (black? fdn n)
                                             (< priority (fdnpriority fdn n))))
                                ins)))))
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
                         ins (fdnin fdn s)
                         bad? (and (white? fdn s)
                                   (black? fdn n)
                                   (every? (fn [s2] (and (white? fdn s2)
                                                         (<= priority (fdnpriority fdn s2))))
                                           (fdnin fdn n))
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
            (let [priority (fdnpriority fdn n)
                  ins (fdnin fdn n)
                  outs (fdnout fdn n)]
              (and (not= :bottom n)
                   (white? fdn n)
                   (or (some (fn [s]
                               (and (black? fdn s)
                                    (<= priority (fdnpriority fdn s))))
                             ins)
                       (some (fn [s]
                               (and (black? fdn s)
                                    (<= priority (fdnpriority fdn s))))
                             outs)))))
          (sort-by fdnstr (nodes fdn))))

(defn spread-color
  [fdn strategy]
  (let [bad-black-strokes-deterministic (white-bad-strokes fdn)
        bad-white-strokes-deterministic (abduce-bad-strokes-deterministic fdn)
        bad-white-strokes-nondeterministic (abduce-bad-strokes-nondeterministic fdn)
        bad-black-nodes-deterministic (white-bad-nodes-deterministic fdn)
        bad-white-nodes-deterministic (abduce-bad-nodes fdn)
        bad-black-nodes-nondeterministic (white-bad-nodes-nondeterministic fdn)
        bad-deterministic (concat bad-black-strokes-deterministic
                                  bad-white-strokes-deterministic
                                  bad-black-nodes-deterministic
                                  bad-white-nodes-deterministic)
        bad-nondeterministic (concat bad-white-strokes-nondeterministic
                                     bad-black-nodes-nondeterministic)]
    (when @debugging?
      (info "\n--- Spreading color.")
      (info "Found bad black strokes (deterministic):" bad-black-strokes-deterministic)
      (info "Found bad white strokes (deterministic):" bad-white-strokes-deterministic)
      (info "Found bad black strokes (nondeterministic):" bad-white-strokes-nondeterministic)
      (info "Found bad black nodes (deterministic):" bad-black-nodes-deterministic)
      (info "Found bad white nodes (deterministic):" bad-white-nodes-deterministic)
      (info "Found bad white nodes (nondeterministic):" bad-black-nodes-nondeterministic)
      (info "\n\n"))
    (if (not-empty bad-deterministic)
      (reduce (fn [fdn2 n-or-s] (if (white? fdn2 n-or-s)
                                  (assert-black fdn2 n-or-s)
                                  (assert-white fdn2 n-or-s)))
              fdn bad-deterministic)
      (let [choice (strategy fdn bad-nondeterministic)]
        (if (white? fdn choice)
          (assert-black fdn choice)
          (assert-white fdn choice))))))

(defn contract
  [fdn nodes & {:keys [strategy] :or {strategy default-strategy}}]
  (assert (sequential? nodes))
  (assert fdn)
  (status "\n\n*** Contracting by" nodes)
  (let [fdn-priority (inc-priority-counter fdn)
        fdn-asserted (reduce assert-white fdn-priority nodes)]
    (loop [fdn-colored (spread-color fdn-asserted strategy)]
      (if (check-color-axioms fdn-colored)
        fdn-colored
        (recur (spread-color fdn-colored strategy))))))

(defn abduce
  [fdn nodes & {:keys [strategy] :or {strategy default-strategy}}]
  (assert (sequential? nodes))
  (assert fdn)
  (status "\n\n*** Abducing by" nodes)
  (let [fdn-priority (inc-priority-counter fdn)
        fdn-asserted-non-initial (reduce assert-black fdn-priority
                                         (filter #(not (initial? fdn-priority %)) nodes))
        fdn-asserted-initial (reduce assert-black-initial fdn-asserted-non-initial
                                     (filter #(initial? fdn-asserted-non-initial %) nodes))]
    (loop [fdn-colored (spread-color fdn-asserted-initial strategy)]
      (if (check-color-axioms fdn-colored)
        fdn-colored
        (recur (spread-color fdn-colored strategy))))))
