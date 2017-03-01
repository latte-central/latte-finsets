(ns latte-finsets.core
  "The formalization of finite sets.
"

  (:refer-clojure :exclude [and or not set])

  (:require [latte.core :as latte :refer [definition defthm defaxiom defnotation
                                          forall lambda ==>
                                          assume have pose proof lambda forall]]
            [latte.quant :as q :refer [exists]]
            [latte.prop :as p :refer [<=> and or not]]
            [latte.equal :as eq :refer [equal]]))


