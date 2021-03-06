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

(defn turn-off-inconsistency-nodes
  []
  (swap! override-visualization-options assoc :inconsistency-nodes :no))

(defn turn-on-inconsistency-nodes
  []
  (swap! override-visualization-options assoc :inconsistency-nodes :yes))

(defn revert-inconsistency-nodes
  []
  (swap! override-visualization-options dissoc :inconsistency-nodes))

(defn visualize-dot
  [fdn node-labels? stroke-labels? priority-labels? inconsistency-nodes? fdnstr-fn]
  (let [inconsistency-nodes? (cond (= :yes (:inconsistency-nodes @override-visualization-options)) true
                                   (= :no (:inconsistency-nodes @override-visualization-options)) false
                                   :else inconsistency-nodes?)
        fdn (if inconsistency-nodes? fdn
                ;; if requested, remove all inconsistency nodes
                (reduce remove-stroke-or-node
                        fdn (conj (filter (fn [s] (and (string? s) (.startsWith s "bot_"))) (strokes fdn))
                                  :bottom)))
        stroke-labels? (cond (= :yes (:stroke-labels @override-visualization-options)) true
                             (= :no (:stroke-labels @override-visualization-options)) false
                             :else stroke-labels?)
        priority-labels? (cond (= :yes (:priority-labels @override-visualization-options)) true
                               (= :no (:priority-labels @override-visualization-options)) false
                               :else priority-labels?)
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
                                                              (if (and stroke-labels?
                                                                       ;; initial strokes don't get labels
                                                                       (not (re-matches #"\..*" s)))
                                                                (format "%s%s"
                                                                        (-> (or (fdnstr-fn s) "")
                                                                            (str/replace #"&" "&and;")
                                                                            (str/replace #"->" "&rarr;")
                                                                            (str/replace #"bot_" "&perp; "))
                                                                        (if priority-labels? (format " (%d)" (fdnpriority fdn s)) ""))
                                                                "&nbsp;")))
                                g-strokes (strokes fdn))
        g-node-labels (reduce (fn [g n] (graphattr/add-attr g n :label
                                                            (if node-labels?
                                                              (format "%s%s"
                                                                      (or (fdnstr-fn n) "")
                                                                      (if priority-labels? (format " (%d)" (fdnpriority fdn n)) ""))
                                                              "&nbsp;")))
                              g-stroke-labels (nodes fdn))]
    ;; add bottom node properties (if bottom node exists)
    (-> g-node-labels
        (graphattr/add-attr :bottom :label "&perp;")
        (graphattr/add-attr :bottom :fontsize "32")
        (graphattr/add-attr :bottom :shape :none))))

(defn visualize
  [fdn & {:keys [node-labels? stroke-labels? priority-labels? inconsistency-nodes? fdnstr-fn]
          :or {node-labels? true stroke-labels? true priority-labels? true inconsistency-nodes? true fdnstr-fn fdnstr}}]
  (graphio/view (visualize-dot fdn node-labels? stroke-labels? priority-labels? inconsistency-nodes? fdnstr-fn)
                :node {:fillcolor :white :style :filled :fontname "sans"}))

(defn save-pdf
  [fdn fname & {:keys [node-labels? stroke-labels? priority-labels? inconsistency-nodes? fdnstr-fn]
               :or {node-labels? true stroke-labels? true priority-labels? false inconsistency-nodes? true fdnstr-fn fdnstr}}]
  (let [dot (graphio/dot-str (visualize-dot fdn node-labels? stroke-labels? priority-labels? inconsistency-nodes? fdnstr-fn)
                             :node {:fillcolor :white :style :filled :fontname "sans"})
        {pdf :out} (shell/sh "dot" "-Tpdf" :in dot :out-enc :bytes)]
    (with-open [w (java.io.FileOutputStream. fname)]
      (.write w pdf))))

