(ns paragon.visualization
  (:require [paragon.core :refer :all]
            [loom.io :as graphio]
            [loom.attr :as graphattr]
            [clojure.string :as str]
            [clojure.java.shell :as shell]))

(defn format-tags
  [fdn stroke-or-node fdnstr-fn]
  (let [tags (fdntags fdn stroke-or-node)]
    (if (empty? tags) ""
        (format "\n%s" (str/join "\n" (for [{:keys [type node color priority]} tags]
                                        (format "%s%s (%d)" (if (= :black color) "+" "-")
                                                (fdnstr-fn node) priority)))))))

(defn visualize-dot
  [fdn node-labels? stroke-labels? tag-labels? fdnstr-fn]
  (let [g (:graph fdn)
        g-nodes (-> g
                    (graphattr/add-attr-to-nodes :shape :ellipse (nodes fdn))
                    (graphattr/add-attr-to-nodes :fillcolor :white (filter #(white? fdn %) (nodes fdn)))
                    (graphattr/add-attr-to-nodes :fillcolor :black (filter #(black? fdn %) (nodes fdn)))
                    (graphattr/add-attr-to-nodes :fontcolor :white (filter #(black? fdn %) (nodes fdn)))
                    (graphattr/add-attr-to-nodes :fontcolor :black (filter #(white? fdn %) (nodes fdn))))
        g-strokes (-> g-nodes
                      (graphattr/add-attr-to-nodes :shape :plain (strokes fdn))
                      (graphattr/add-attr-to-nodes :height 0.1 (strokes fdn))
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
                                                                        (if tag-labels? (format-tags fdn s fdnstr-fn) ""))
                                                                "&nbsp;")))
                                g-strokes (strokes fdn))
        g-node-labels (reduce (fn [g n] (graphattr/add-attr g n :label
                                                            (if node-labels?
                                                              (format "%s%s"
                                                                      (or (fdnstr-fn n) "")
                                                                      (if tag-labels? (format-tags fdn n fdnstr-fn) ""))
                                                              "&nbsp;")))
                              g-stroke-labels (nodes fdn))]
    ;; add bottom node properties (if bottom node exists)
    (-> g-node-labels
        (graphattr/add-attr :bottom :label "&perp;")
        (graphattr/add-attr :bottom :fontsize "32")
        (graphattr/add-attr :bottom :shape :none))))

(defn visualize
  [fdn & {:keys [node-labels? stroke-labels? tag-labels? fdnstr-fn]
          :or {node-labels? true stroke-labels? true tag-labels? true fdnstr-fn fdnstr}}]
  (graphio/view (visualize-dot fdn node-labels? stroke-labels? tag-labels? fdnstr-fn)
                :node {:fillcolor :white :style :filled :fontname "sans"}))

(defn save-pdf
  [fdn fname & {:keys [node-labels? stroke-labels? tag-labels? fdnstr-fn]
               :or {node-labels? true stroke-labels? true tag-labels? false fdnstr-fn fdnstr}}]
  (let [dot (graphio/dot-str (visualize-dot fdn node-labels? stroke-labels? tag-labels? fdnstr-fn)
                             :node {:fillcolor :white :style :filled :fontname "sans"})
        {pdf :out} (shell/sh "dot" "-Tpdf" :in dot :out-enc :bytes)]
    (with-open [w (java.io.FileOutputStream. fname)]
      (.write w pdf))))

