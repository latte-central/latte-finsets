(ns latte-finsets.finite
  "The property of a set to be finite."

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

            [latte-finsets.range :as r :refer [range]]))

(definition finite-prop
  "The property a finite set must fulfill."
  [[?T :type] [s (set T)] [n nat] [f (rel nat T)]]
  (pfun/bijection f (range one n) s))

(definition finite
  "The definition of a finite set (of cardinal `n`)."
  [[?T :type] [s (set T)]]
  (exists [n nat]
    (prel/rel-ex (lambda [f (rel nat T)]
                   (finite-prop s n f)))))

(definition fin
  "The canonical finite set of size `n`."
  [n nat]
  (range one n))

(defthm fin-zero
  []
  (set/seteq (fin zero) (set/emptyset nat)))

(proof 'fin-zero
  (qed (r/emptyrange-emptyset)))

(defthm fin-finite
  [n nat]
  (finite (fin n)))

(proof 'fin-finite
  (have <a> (finite-prop (range one n) n (rel/identity nat))
        :by (pfun/ridentity-bijection (range one n)))
  
  (have <b> _ :by ((prel/rel-ex-intro (lambda [f (rel nat nat)]
                                        (finite-prop (range one n) n f)) (rel/identity nat)) 
                   <a>))

  (have <c> _ :by ((q/ex-intro (lambda [$ nat]
                                 (prel/rel-ex (lambda [f (rel nat nat)]
                                                (finite-prop (range one n) $ f)))) n)
                   <b>))

  (qed <c>))

(defthm emptyset-finite
  [T :type]
  (finite (set/emptyset T)))

(proof 'emptyset-finite
  "We select n=zero and f=emptyrel"

  (pose P := (lambda [s (set nat)]
               (pfun/bijection (rel/emptyrel nat T) s (set/emptyset T))))

  (have <a> (P (set/emptyset nat))
        :by (pfun/emptyrel-bijection nat T))

  (have <b> (seteq (set/emptyset nat) (range one zero))
        :by ((set/seteq-sym (range one zero) (set/emptyset nat))
             (r/emptyrange-emptyset)))

  (have <c> (P (range one zero))
        :by ((set/seteq-subst-prop P (set/emptyset nat) (range one zero))
             <b> <a>))

  (have <d> _ :by ((prel/rel-ex-intro (lambda [f (rel nat T)]
                                        (finite-prop (set/emptyset T) zero f))
                      (rel/emptyrel nat T)) <c>))

  (have <e> _ :by ((q/ex-intro (lambda [$ nat]
                                 (prel/rel-ex (lambda [f (rel nat T)]
                                                (finite-prop (set/emptyset T) $ f))))
                               zero)
                   <d>))

  (qed <e>))

