(ns latte-finsets.core
  "The formalization of finite sets.
"

  (:refer-clojure :exclude [and or not set <= int])

  (:require [latte.core :as latte :refer [definition defthm defaxiom defnotation
                                          forall lambda defimplicit
                                          assume have pose proof lambda forall]]
            [latte.quant :as q :refer [exists]]
            [latte.prop :as p :refer [<=> and or not]]
            [latte.equal :as eq :refer [equal]]

            [latte-sets.core :as set :refer [set]]
            [latte-sets.rel :as rel :refer [rel]]
            [latte-sets.pfun :as pfun :refer [pfun]]
                       
            [latte-integers.core :as int :refer [int]]
            [latte-integers.nat :as nat :refer [nat]]
            [latte-integers.ord :as ord :refer [<=]]))

(definition range
  "The range set from `m` to `n`."
  [[m int] [n int]]
  (lambda [k int]
    (and (<= m k)
         (<= k n))))

(definition counted-def
  "The set `s` is counted from 1 to `n`"
  [[T :type] [s (set T)] [n int]]
  (exists [cf (rel T int)]
    (exists [pf (pfun cf s (range int/one n))]
      (pfun/pbijective pf))))





