(defproject latte-finsets "0.1.0-SNAPSHOT"
  :description "A formalization of finite sets in LaTTe."
  :url "https://github.com/fredokun/latte-sets.git"
  :license {:name "MIT Licence"
            :url "http://opensource.org/licenses/MIT"}
  :dependencies [[org.clojure/clojure "1.8.0"]
                 [latte "0.6.1-SNAPSHOT"]
                 [latte-sets "0.1.2-SNAPSHOT"]
                 [latte-integers "0.5.8-SNAPSHOT"]]
  :codox {:output-path "docs"
          :metadata {:doc/format :markdown}
          :namespaces [latte-finsets.core
                       ]}
  :plugins [[lein-codox "0.10.2"]])
