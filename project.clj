(defproject latte-finsets "0.1.0-SNAPSHOT"
  :description "A formalization of finite sets in LaTTe."
  :url "https://github.com/fredokun/latte-sets.git"
  :license {:name "MIT Licence"
            :url "http://opensource.org/licenses/MIT"}
  :dependencies [[org.clojure/clojure "1.10.1"]
                 [latte "1.0b3-SNAPSHOT"]
                 [latte-prelude "1.0b3-SNAPSHOT"]
                 [latte-sets "1.0b3-SNAPSHOT"]
                 [latte-integers "0.10.0-SNAPSHOT"]]
  :codox {:output-path "docs"
          :metadata {:doc/format :markdown}
          :namespaces [latte-finsets.core
                       ]}
  :plugins [[lein-codox "0.10.6"]])
