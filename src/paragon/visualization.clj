(ns paragon.visualization
  (:require [paragon.core :refer :all]
            [loom.io :as graphio]
            [loom.attr :as graphattr]
            [clojure.string :as str]
            [clojure.java.shell :as shell]))

(def override-visualization-options (atom {}))

(defn turn-off-stroke-labels
  []
  (swap! override-visualization-options assoc :stroke-labels :no))

(defn turn-on-stroke-labels
  []
  (swap! override-visualization-options assoc :stroke-labels :yes))

(defn revert-stroke-labels
  []
  (swap! override-visualization-options dissoc :stroke-labels))

(defn turn-off-priority-labels
  []
  (swap! override-visualization-options assoc :priority-labels :no))

(defn turn-on-priority-labels
  []
  (swap! override-visualization-options assoc :priority-labels :yes))

(defn revert-priority-labels
  []
  (swap! override-visualization-options dissoc :priority-labels))

(defn turn-off-fluent-labels
  []
  (swap! override-visualization-options assoc :fluent-labels :no))

(defn turn-on-fluent-labels
  []
  (swap! override-visualization-options assoc :fluent-labels :yes))

(defn revert-fluent-labels
  []
  (swap! override-visualization-options dissoc :fluent-labels))

(defn visualize-dot
  [fdn node-labels? stroke-labels? priority-labels? fluent-labels? fdnstr-fn]
  (let [stroke-labels? (cond (= :yes (:stroke-labels @override-visualization-options)) true
                             (= :no (:stroke-labels @override-visualization-options)) false
                             :else stroke-labels?)
        priority-labels? (cond (= :yes (:priority-labels @override-visualization-options)) true
                               (= :no (:priority-labels @override-visualization-options)) false
                               :else priority-labels?)
        fluent-labels? (cond (= :yes (:fluent-labels @override-visualization-options)) true
                             (= :no (:fluent-labels @override-visualization-options)) false
                             :else fluent-labels?)
        g (:graph fdn)
        g-nodes (-> g
                    (graphattr/add-attr-to-nodes :shape :ellipse (nodes fdn))
                    (graphattr/add-attr-to-nodes :fillcolor :white (filter #(white? fdn %) (nodes fdn)))
                    (graphattr/add-attr-to-nodes :fillcolor :black (filter #(black? fdn %) (nodes fdn)))
                    (graphattr/add-attr-to-nodes :fontcolor :white (filter #(black? fdn %) (nodes fdn)))
                    (graphattr/add-attr-to-nodes :fontcolor :black (filter #(white? fdn %) (nodes fdn))))
        g-strokes (-> g-nodes
                      (graphattr/add-attr-to-nodes :shape (if stroke-labels? :box :underline) (strokes fdn))
                      (graphattr/add-attr-to-nodes :height 0.1 (strokes fdn))
                      (graphattr/add-attr-to-nodes :fixedsize (if stroke-labels? "false" "true") (strokes fdn))
                      (graphattr/add-attr-to-nodes :fillcolor :white (filter #(white? fdn %) (strokes fdn)))
                      (graphattr/add-attr-to-nodes :fillcolor :black (filter #(black? fdn %) (strokes fdn)))
                      (graphattr/add-attr-to-nodes :fontcolor :white (filter #(black? fdn %) (strokes fdn)))
                      (graphattr/add-attr-to-nodes :fontcolor :black (filter #(white? fdn %) (strokes fdn))))
        g-stroke-labels (reduce (fn [g s] (graphattr/add-attr g s :label
                                                              (if stroke-labels?
                                                                (let [ss (or (fdnstr-fn s) "")
                                                                      bot? (re-matches #"bot_.*" ss)
                                                                      ss-nobot (str/replace s #"^bot_" "")
                                                                      init? (initial-stroke? fdn s)]
                                                                  (format "%s%s%s"
                                                                          (cond
                                                                            init?
                                                                            (if (and fluent-labels? (not-empty (fdnfluents fdn s)))
                                                                              (format "(%s)" (str/join ", " (map name (fdnfluents fdn s)))) "")
                                                                            (re-find #"->" ss-nobot)
                                                                            (format "%s%s&rarr;%s" (if bot? "&perp;" "")
                                                                                    (str/join "&and;"
                                                                                              (map (fn [n] (format "%s%s" (fdnstr n)
                                                                                                                   (if (and fluent-labels? (not-empty (fdnfluents fdn n)))
                                                                                                                     (format "(%s)" (str/join ", " (map name (fdnfluents fdn n))))
                                                                                                                     "")))
                                                                                                   (fdnin fdn s)))
                                                                                    (format "%s%s" (fdnstr (first (fdnout fdn s)))
                                                                                            (if (and fluent-labels? (not-empty (fdnfluents fdn (first (fdnout fdn s)))))
                                                                                              (format "(%s)" (str/join ", " (map name (fdnfluents fdn (first (fdnout fdn s))))))
                                                                                              "")))
                                                                            :else
                                                                            (format "%s%s"
                                                                                    (if bot? (format "&perp; " ss-nobot) ss-nobot)
                                                                                    (if (and fluent-labels? (not-empty (fdnfluents fdn s)))
                                                                                      (format "(%s)" (str/join ", " (map name (fdnfluents fdn s)))) "")))
                                                                          (if (and (not init?) priority-labels?) (format " [%d]" (fdnpriority fdn s)) "")
                                                                          (if-let [desc (:desc (get-stroke-constraint fdn s))]
                                                                            (format "\n%s\n" desc) "")))
                                                                "&nbsp;")))
                                g-strokes (strokes fdn))
        g-node-labels (reduce (fn [g n] (graphattr/add-attr g n :label
                                                            (if node-labels?
                                                              (format "%s%s%s"
                                                                      (or (fdnstr-fn n) "")
                                                                      (if (and fluent-labels? (not-empty (fdnfluents fdn n)))
                                                                        (format "(%s)" (str/join ", " (map name (fdnfluents fdn n)))) "")
                                                                      (if priority-labels? (format " [%d]" (fdnpriority fdn n)) ""))
                                                              "&nbsp;")))
                              g-stroke-labels (nodes fdn))]
    ;; add bottom node properties (if bottom node exists)
    (-> g-node-labels
        (graphattr/add-attr :bottom :label "&perp;")
        (graphattr/add-attr :bottom :fontsize "32")
        (graphattr/add-attr :bottom :shape :none))))

(defn visualize
  [fdn & {:keys [node-labels? stroke-labels? priority-labels? fluent-labels? fdnstr-fn]
          :or {node-labels? true stroke-labels? true priority-labels? true fluent-labels? true fdnstr-fn fdnstr}}]
  (graphio/view (visualize-dot fdn node-labels? stroke-labels? priority-labels? fluent-labels? fdnstr-fn)
                :node {:fillcolor :white :style :filled :fontname "sans"}))

(defn save-pdf
  [fdn fname & {:keys [node-labels? stroke-labels? priority-labels? fluent-labels? fdnstr-fn]
               :or {node-labels? true stroke-labels? true priority-labels? false fluent-labels? true fdnstr-fn fdnstr}}]
  (let [dot (graphio/dot-str (visualize-dot fdn node-labels? stroke-labels? priority-labels? fluent-labels? fdnstr-fn)
                             :node {:fillcolor :white :style :filled :fontname "sans"})
        {pdf :out} (shell/sh "dot" "-Tpdf" :in dot :out-enc :bytes)]
    (with-open [w (java.io.FileOutputStream. fname)]
      (.write w pdf))))

