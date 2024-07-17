(defproject latte-finsets "0.2.0-SNAPSHOT"
  :description "A formalization of finite sets in LaTTe."
  :url "https://github.com/fredokun/latte-sets.git"
  :license {:name "MIT Licence"
            :url "http://opensource.org/licenses/MIT"}
  :dependencies [[org.clojure/clojure "1.10.1"]
                 [latte "1.0b10-SNAPSHOT"]
                 [latte-sets "1.0b10-SNAPSHOT"]
                 [latte-nats "0.7.0-SNAPSHOT"]]
  :codox {:output-path "docs"
          :metadata {:doc/format :markdown}
          :namespaces [latte-finsets.range
                       latte-finsets.finite
                       ]}
  :plugins [[lein-codox "0.10.8"]])
