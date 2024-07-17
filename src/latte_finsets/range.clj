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

(comment ;; TODO (if needed)

(defthm range-pred
  [[m n nat]]
  (==> (<= m n)
       (seteq (set/remove n (range m n))
              (range m (pred n)))))

(try-proof 'range-pred
  (assume [Hmn _]
    
    "Subset case"
    
    (assume [k nat
             Hk (elem k (set/remove (n range m n)))]

      "We have to show that (<= m k) and (<= k (pred n))"

      (have <a1> (and (and (<= m k) (<= k n))
                      (not (= k n))) :by Hk)

      (have <a> (<= m k) :by (p/and-elim-left (p/and-elim-left <a1>)))

      (have <b1> (< k n) :by ((ord/lt-le-ne k n) 
                              (p/and-elim-right (p/and-elim-left <a1>))
                              (p/and-elim-right <a1>)))

      

)))
)
