(ns latte-finsets.range
  "The (finite) range [m;n]  (with m, n natural numbers)
"

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
            [latte-nats.minus :as minus :refer [pred -]]
            [latte-nats.ord :as ord :refer [< <=]]))

(definition range
  "The range set from `m` to `n` (inclusive)."
  [[m nat] [n nat]]
  (lambda [k nat]
    (and (<= m k)
         (<= k n))))

(defthm range-empty-cond
  [[m nat] [n nat]]
  (==> (< n m)
       (forall [k nat] (not (elem k (range m n))))))

(proof 'range-empty-cond
  (assume [Hinf (< n m)]
    (assume [k nat
             Hk (elem k (range m n))]
      (have <a> (<= m n) :by ((ord/le-trans m k n)
                              (p/and-elim-left Hk)
                              (p/and-elim-right Hk)))
      (have <b> (<= n m) :by (p/and-elim-left Hinf))
      (have <c> (= n m) :by ((ord/le-antisym n m) <b> <a>))
      (have <d> p/absurd :by ((p/absurd-intro (= n m)) <c> (p/and-elim-right Hinf)))))
  (qed <d>))

(definition emptyrange
  "The canonical empty range"
  []
  (range one zero))

(defthm range-empty-one-zero
  []
  (forall [k nat] (not (elem k emptyrange))))

(proof 'range-empty-one-zero
  (have <a> (< zero one) :by (ord/lt-succ zero))
  (qed ((range-empty-cond one zero) <a>)))

(defthm range-empty-emptyset
  [[m n nat]]
  (==> (< n m)
       (set/seteq (range m n) (set/emptyset nat))))

(proof 'range-empty-emptyset
  (assume [Hmn _]
    "Subset case"
    (assume [k nat
             Hk (elem k (range m n))]
      (have <a1> p/absurd :by ((range-empty-cond m n) Hmn k Hk))
      (have <a> (elem k (set/emptyset nat)) :by (<a1> (elem k (set/emptyset nat)))))
    
    "Superset case"
    (assume [k nat
             Hk (elem k (set/emptyset nat))]
      (have <b> (elem k (range m n)) :by (Hk (elem k (range m n)))))

    (have <c> _ :by (p/and-intro <a> <b>)))

  (qed <c>))

(defthm emptyrange-emptyset
  []
  (set/seteq emptyrange (set/emptyset nat)))

(proof 'emptyrange-emptyset
  (have <a> (< zero one) :by (ord/lt-succ zero))
  (qed ((range-empty-emptyset one zero) <a>)))
 
(defthm range-one-eq
  [[m nat] [n nat]]
  (==> (= m n)
       (forall [k nat]
         (==> (elem k (range m n))
              (= k n)))))

(proof 'range-one-eq
  (assume [Heq (= m n)
           k nat
           Hk (elem k (range m n))]
    (have <a> (elem k (range n n))
          :by (eq/rewrite Hk Heq))
    (have <b> (<= n k) :by (p/and-elim-left <a>))
    (have <c> (<= k n) :by (p/and-elim-right <a>))
    (have <d> (= k n) :by (eq/eq-sym ((ord/le-antisym n k) <b> <c>))))
  (qed <d>))

(defthm range-one
  [[n nat]]
  (forall-in [k (range n n)]
    (= k n)))

(proof 'range-one
  (have <a> (= n n) :by (eq/eq-refl n))
  (qed  ((range-one-eq n n) <a>)))

(defthm range-pred
  [[m n nat]]
  (==> (<> n zero)
       (<= m n)
       (seteq (set/remove n (range m n))
              (range m (pred n)))))

(proof 'range-pred
  (assume [Hnz _
           Hmn _]
    
    "Subset case"
    
    (assume [k nat
             Hk (elem k (set/remove n (range m n)))]

      "We have to show that (<= m k) and (<= k (pred n))"

      (have <a> (and (not (= k n))
                     (and (<= m k) (<= k n))) :by Hk)

      (have <b> (<= m k) :by (p/and-elim-left (p/and-elim-right <a>)))
      
      
      (have <c1> (<= k n) :by (p/and-elim-right (p/and-elim-right <a>)))

      (have <c2> (< k n) :by ((ord/lt-le-ne k n)
                              <c1> (p/and-elim-left <a>)))

      (have <c> (<= k (pred n)) :by ((ord/lt-le-pred k n) <c2>))

      
      (have <d> (elem k (range m (pred n)))
            :by (p/and-intro <b> <c>)))


    "Superset case"

    (assume [k nat
             Hk (elem k (range m (pred n)))]
     
      "We have to show (elem k (set/remove n (range m n)))"
      "which means: (and (not (equal k n))
                         (elem k (range m n)))"

      (assume [Hcontra (equal k n)]
        (have <e1> (<= k (pred n)) :by (p/and-elim-right Hk))
        (have <e2> (<= k (pred k)) :by (eq/rewrite <e1> (eq/eq-sym Hcontra)))
        (have <e3> (<= (pred k) k) :by (ord/le-pred k))
        (have <e4> (= (pred k) k) :by ((ord/le-antisym (pred k) k) <e3> <e2>))
        (have <e5> (= k zero) :by ((minus/pred-eq-zero k) <e4>))
        (have <e6> (= n zero) :by (eq/rewrite <e5> Hcontra))
        (have <e> p/absurd :by (Hnz <e6>)))

      (have <f1> (<= m k) :by (p/and-elim-left Hk))
      (have <f2> (<= (pred n) n) :by (ord/le-pred n))
      (have <f3> (<= k (pred n)) :by (p/and-elim-right Hk))
      (have <f4> (<= k n) :by ((ord/le-trans k (pred n) n) <f3> <f2>))
      (have <f> (elem k (range m n)) :by (p/and-intro <f1> <f4>))

      (have <g> (elem k (set/remove n (range m n)))
            :by (p/and-intro <e> <f>)))


    (have <h> _ :by (p/and-intro <d> <g>)))

  (qed <h>))





