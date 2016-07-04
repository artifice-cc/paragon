(ns paragon.dbcompletion-test
  (:require [clojure.test :refer :all]
            [paragon.dbcompletion :refer :all]
            [paragon.core :refer :all]
            [paragon.coloring :refer :all]
            [paragon.visualization :refer :all]
            [clojure.pprint]))

(deftest test-florida-keys-zips
  (turn-off-debugging)
  (turn-off-inconsistency-nodes)
  (let [headers ["zip" "city" "state"]
        zips [["33036" "Islamorada" "FL"]
              ["33037" "Port Largo" "FL"]
              ["33037" "Key Largo" "FL"]
              ["33039" "Homestead" "FL"]
              ["33040" "Stock Island" "FL"]
              ["33040" "Key West" "FL"]
              ["33040" "Bay Point" "FL"]
              ["33040" "Bay Point Key" "FL"]
              ["33040" "Big Coppitt Key" "FL"]
              ["33041" "Key West" "FL"]
              ["33042" "Sugarloaf" "FL"]
              ["33042" "Sugarloaf Shores" "FL"]
              ["33042" "Cudjoe Key" "FL"]
              ["33043" "Big Pine Key" "FL"]
              ["33043" "Bahia Honda Key" "FL"]
              ["33045" "Key West" "FL"]
              ["33050" "Center Island" "FL"]
              ["33050" "Duck Key" "FL"]
              ["33050" "Conch Key" "FL"]
              ["33050" "Marathon" "FL"]]
        fdn-small (build-fdn-from-headers-rows
                   headers zips
                   [#{"city:Sugarloaf" "city:Sugarloaf Key" "city:Sugarloaf Shores"}
                    #{"city:Bay Point" "city:Bay Point Key"}])
        fdn-small-1 (abduce fdn-small ["zip:33050"])
        _ (prn (believed fdn-small-1))
        fdn-all-zips (time (build-fdn-from-csv
                            "/Users/JoshuaEckroth/Documents/git/waterlevels/forms/us_postal_codes.csv"
                            [0 1 3]
                            {}))
        fdn-all-1 (time (abduce fdn-all-zips ["zip:33050"]))
        _ (prn (believed fdn-all-1))
        fdn-oilfield-places (time (build-fdn-from-csv
                                   "/Users/JoshuaEckroth/Documents/i2k/i2kdata/context/Oilfield Places.csv"
                                   [0 2 7 8 9 10 11 12 13 14 15 16 17 19 23 24]
                                   {}))
        fdn-oilfield-1 (time (abduce fdn-oilfield-places ["Country:Albania"]))
        _ (prn (believed fdn-oilfield-1))]
    #_(visualize fdn-small-1)
    
    ))
