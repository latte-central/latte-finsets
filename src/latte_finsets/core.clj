(ns latte-finsets.core
  "The formalization of finite sets.
"

  (:refer-clojure :exclude [and or not set <= < = int])

  (:require [latte.core :as latte :refer [definition defthm defaxiom defnotation
                                          forall lambda defimplicit deflemma qed
                                          assume have pose proof lambda forall]]
            [latte.quant :as q :refer [exists]]
            [latte.prop :as p :refer [<=> and or not]]
            [latte.equal :as eq :refer [equal]]

            [latte-sets.core :as set :refer [set elem forall-in exists-in]]
            [latte-sets.rel :as rel :refer [rel]]
            [latte-sets.pfun :as pfun :refer [pfun]]
                       
            [latte-integers.core :as int :refer [int =]]
            [latte-integers.nat :as nat :refer [nat]]
            [latte-integers.ord :as ord :refer [< <=]]))

(definition range
  "The range set from `m` to `n`."
  [[m int] [n int]]
  (lambda [k int]
    (and (<= m k)
         (<= k n))))

(defthm range-empty
  [[m int] [n int]]
  (==> (< n m)
       (forall [k int] (not (elem k (range m n))))))

(proof 'range-empty
  (assume [Hinf (< n m)]
    (assume [k int
             Hk (elem k (range m n))]
      (have <a> (<= m n) :by ((ord/le-trans m k n)
                              (p/and-elim-left Hk)
                              (p/and-elim-right Hk)))
      (have <b> (<= n m) :by (p/and-elim-left Hinf))
      (have <c> (= n m) :by ((ord/le-antisym n m) <b> <a>))
      (have <d> p/absurd :by ((p/absurd-intro (= n m)) <c> (p/and-elim-right Hinf)))))
  (qed <d>))

(definition counted-def
  "The set `s` is counted from 1 to `n`"
  [[T :type] [s (set T)] [n int] [cf (rel T int)]]
  (and (pfun cf s (range int/one n))
       (pfun/pbijective cf s (range int/one n))))

(defimplicit counted
  "The set `s` is counted from 1 to `n`, cf. [[counted-def]]"
  [def-env ctx [s s-ty] [n n-ty] [cf cf-ty]]
  (let [[T _] (rel/fetch-rel-type def-env ctx cf-ty)]
    (list #'counted-def T s n cf)))

(definition finite-def
  "The definition of a finite set: `s` is finite
if the function `cf` counts the number `n` of elements in `s`,
 see [[counted]]."
  [[T :type] [s (set T)] [cf (rel T int)]]
  (exists [n int]
    (counted s n cf)))

;; Remark : the counting function must be passed
;; as a parameter because we cannot existentially
;; quantify over it... (universe issue?)

(defimplicit finite
  "The set `s` is finite according to counting function `cf`, see [[finite-def]]."
  [def-env ctx [s s-ty] [cf cf-ty]]
  (let [T (set/fetch-set-type def-env ctx s-ty)]
    (list #'finite-def T s cf)))


;; the emptyset case

(deflemma emptyset-pfun
  [[T :type] [U :type] [f (rel T U)] [to (set U)]]
  (pfun f (set/emptyset T) to))

(proof 'emptyset-pfun
  (assume [x T
           Hx (elem x (set/emptyset T))]
    (have <a> p/absurd :by Hx)
    (have <b> _ :by (Hx (forall-in [y1 U to]
                                   (forall-in [y2 U to]
                                              (==> (f x y1)
                                                   (f x y2)
                                                   (equal y1 y2)))))))
  (qed <b>))

(deflemma emptyset-pinjective
  [[T :type] [U :type] [f (rel T U)] [to (set U)]]
  (pfun/pinjective f (set/emptyset T) to))

(proof 'emptyset-pinjective
  (assume [x1 T
           Hx1 (elem x1 (set/emptyset T))]
    (have <a> p/absurd :by Hx1)
    (have <b> _ :by (Hx1 (forall-in [x2 T (set/emptyset T)]
                           (forall-in [y1 U to]
                             (forall-in [y2 U to]
                               (==> (f x1 y1)
                                    (f x2 y2)
                                    (equal y1 y2)
                                    (equal x1 x2))))))))
  (qed <b>))

(deflemma emptyset-psurjective
  [[T :type] [cf (rel T int)]]
  (pfun/psurjective cf (set/emptyset T) (range int/one int/zero)))

(proof 'emptyset-psurjective
  (assume [y int
           Hy (elem y (range int/one int/zero))]
    (have <a> (< int/zero int/one) :by (ord/lt-succ int/zero))
    (have <b> (not (elem y (range int/one int/zero)))
          :by ((range-empty int/one int/zero)
               <a> y))
    (have <c> p/absurd :by (<b> Hy))
    (have <d> _ :by (<c> (exists-in [x T (set/emptyset T)]
                           (cf x y)))))
  (qed <d>))

(deflemma emptyset-counted
  [[T :type] [cf (rel T int)]]
  (counted (set/emptyset T) int/zero cf))

(proof 'emptyset-counted
  (qed (p/and-intro (emptyset-pfun T int cf (range int/one int/zero))
                    (p/and-intro (emptyset-pinjective T int cf (range int/one int/zero))
                                 (emptyset-psurjective T cf)))))

(defthm finite-emptyset-thm
  "The emptyset of type `T` is finite, whatever the counting function."
  [[T :type] [cf (rel T int)]]
  (finite (set/emptyset T) cf))

(proof 'finite-emptyset-thm
  (qed ((q/ex-intro (lambda [k int]
                      (counted (set/emptyset T) k cf))
                    int/zero)
        (emptyset-counted T cf))))

(definition zero-count
  "This is a dummy counting function for use in [[finite-emptyset]]."
  [[T :type]]
  (lambda [x T]
    (lambda [k int]
      (= k int/zero))))

(defimplicit finite-emptyset
  "The emptyset is finite, cf. [[finite-emptyset-thm]]"
  [def-env ctx [T T-ty]]
  (list #'finite (list #'set/emptyset T) (list #'zero-count T)))







