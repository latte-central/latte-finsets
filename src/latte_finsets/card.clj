(ns latte-finsets.card
  "The cardinal of a finite set."

  (:refer-clojure :exclude [and or not set <= < = int range = -])

  (:require [latte.core :as latte :refer [definition try-definition
                                          defthm try-defthm defaxiom defnotation
                                          forall lambda defimplicit deflemma qed
                                          assume have pose proof try-proof lambda forall]]
            [latte-prelude.quant :as q :refer [exists]]
            [latte-prelude.prop :as p :refer [<=> and or not]]
            [latte-prelude.equal :as eq :refer [equal]]

            [latte-sets.set :as set :refer [set elem subset seteq]]
            [latte-sets.algebra :as sa]
            [latte-sets.quant :as sq :refer [forall-in exists-in]]
            [latte-sets.rel :as rel :refer [rel]]
            [latte-sets.powerrel :as prel]
            [latte-sets.pfun :as pfun]
                       
            [latte-nats.core :as nat :refer [zero one succ nat = <>]]

            [latte-finsets.range :as r :refer [range]]
            [latte-finsets.finite :as f :refer [finite]]
            
            ))

(defthm single-card
  [[?T :type] [s (set T)]]
  (forall [n1 n2 nat]
    (==> (prel/rel-ex (lambda [f (rel nat T)]
                        (f/finite-prop s n1 f)))
         (prel/rel-ex (lambda [f (rel nat T)]
                        (f/finite-prop s n2 f)))
         (= n1 n2))))

(try-proof 'single-card-thm
  (assume [n1 _ n2 _
           Hn1 _ Hn2 _]
    (assume [f1 (rel nat T)
             Hf1 (f/finite-prop s n1 f1)]
      (assume [f2 (rel nat T)
               Hf2 (f/finite-prop s n2 f2)]
        ;;(have <a1> (exists-in [x s] (f1 x n1))))
      
      )

)))
