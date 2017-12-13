(defproject latte-finsets "0.1.0-SNAPSHOT"
  :description "A formalization of finite sets in LaTTe."
  :url "https://github.com/fredokun/latte-sets.git"
  :license {:name "MIT Licence"
            :url "http://opensource.org/licenses/MIT"}
  :dependencies [[org.clojure/clojure "1.9.0"]
                 [latte "0.100.0-SNAPSHOT"]
                 [latte-sets "0.5.0-SNAPSHOT"]
                 [latte-integers "0.7.1-SNAPSHOT"]]
  :codox {:output-path "docs"
          :metadata {:doc/format :markdown}
          :namespaces [latte-finsets.core
                       ]}
  :plugins [[lein-codox "0.10.3"]])
