(ns paragon.visualization
  (:require [paragon.core :refer :all]
            [loom.io :as graphio]
            [loom.attr :as graphattr]
            [clojure.java.shell :as shell]))

(defn visualize-dot
  [jg node-labels? stroke-labels? jgstr-fn]
  (let [g (:graph jg)
        g-nodes (-> g
                    (graphattr/add-attr-to-nodes :fillcolor :white (filter #(white? jg %) (nodes jg)))
                    (graphattr/add-attr-to-nodes :fillcolor :black (filter #(black? jg %) (nodes jg)))
                    (graphattr/add-attr-to-nodes :fontcolor :white (filter #(black? jg %) (nodes jg)))
                    (graphattr/add-attr-to-nodes :fontcolor :black (filter #(white? jg %) (nodes jg))))
        g-strokes (-> g-nodes
                      (graphattr/add-attr-to-nodes :shape :plain (strokes jg))
                      (graphattr/add-attr-to-nodes :height 0.1 (strokes jg))
                      (graphattr/add-attr-to-nodes :fillcolor :white (filter #(white? jg %) (strokes jg)))
                      (graphattr/add-attr-to-nodes :fillcolor :black (filter #(black? jg %) (strokes jg)))
                      (graphattr/add-attr-to-nodes :fontcolor :white (filter #(black? jg %) (strokes jg)))
                      (graphattr/add-attr-to-nodes :fontcolor :black (filter #(white? jg %) (strokes jg))))
        g-stroke-labels (reduce (fn [g s] (graphattr/add-attr g s :label (if stroke-labels? (jgstr-fn s) "&nbsp;")))
                                g-strokes (strokes jg))
        g-node-labels (reduce (fn [g n] (graphattr/add-attr g n :label (if node-labels? (jgstr-fn n) "&nbsp;")))
                              g-stroke-labels (nodes jg))]
    ;; add bottom node properties (if bottom node exists)
    (-> g-node-labels
        (graphattr/add-attr :bottom :label "&perp;")
        (graphattr/add-attr :bottom :fontsize "32")
        (graphattr/add-attr :bottom :shape :none))))

(defn visualize
  [jg & {:keys [node-labels? stroke-labels? jgstr-fn]
         :or {node-labels? true stroke-labels? false jgstr-fn jgstr}}]
  (graphio/view (visualize-dot jg node-labels? stroke-labels? jgstr-fn)
                :node {:fillcolor :white :style :filled :fontname "sans"}))

(defn save-pdf
  [jg fname & {:keys [node-labels? stroke-labels? jgstr-fn]
               :or {node-labels? true stroke-labels? false jgstr-fn jgstr}}]
  (let [dot (graphio/dot-str (visualize-dot jg node-labels? stroke-labels? jgstr-fn)
                             :node {:fillcolor :white :style :filled :fontname "sans"})
        {pdf :out} (shell/sh "dot" "-Tpdf" :in dot :out-enc :bytes)]
    (with-open [w (java.io.FileOutputStream. fname)]
      (.write w pdf))))

