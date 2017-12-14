(ns latte-finsets.core
  "The formalization of finite sets.
"

  (:refer-clojure :exclude [and or not set <= < = int range])

  (:require [latte.core :as latte :refer [definition defthm defaxiom defnotation
                                          forall lambda defimplicit deflemma qed
                                          assume have pose proof lambda forall]]
            [latte.utils :as utils]
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
  [[T :type] [s (set T)] [cf (rel T int)] [n int]]
  (and (pfun cf s (range int/one n))
       (pfun/pbijective cf s (range int/one n))))

(defimplicit counted
  "The set `s` is counted from 1 to `n`, cf. [[counted-def]]"
  [def-env ctx [s s-ty] [cf cf-ty] [n n-ty]]
  (let [[T _] (rel/fetch-rel-type def-env ctx cf-ty)]
    (list #'counted-def T s cf n)))

;; since we want `counted` to be opaque we need introduction and eliminations rules.

(defthm counted-intro-thm
  "The introduction rule for the counted predicate."
  [[T :type] [s (set T)] [cf (rel T int)] [n int]]
  (==> (pfun cf s (range int/one n))
       (pfun/pbijective cf s (range int/one n))
       (counted s cf n)))

(proof 'counted-intro-thm
  (assume [H1 (pfun cf s (range int/one n))
           H2 (pfun/pbijective cf s (range int/one n))]
    (have <a> (counted s cf n) :by (p/and-intro H1 H2)))
  (qed <a>))

(defimplicit counted-intro
  "The introduction rule for the [[counted]] predicate, cf. [[counted-intro-thm]]."
  [def-env ctx [s s-ty] [cf cf-ty] [n int]]
  (let [T (set/fetch-set-type def-env ctx s-ty)]
    (list #'counted-intro-thm T s cf n)))

(defthm counted-elim-pfun-thm
  "The first elimination rule for the [[counted]] predicate: the counted relation
must be a partial function."
  [[T :type] [s (set T)] [cf (rel T int)] [n int]]
  (==> (counted s cf n)
       (pfun cf s (range int/one n))))

(proof 'counted-elim-pfun-thm
  (assume [H (counted s cf n)]
    (have <a> _ :by (p/and-elim-left H)))
  (qed <a>))

(defimplicit counted-elim-pfun
  "The first elimination rule for the [[counted]] predicate: the counted relation
must be a partial function, cf. [[counted-elim-pfun-thm]]."
  [def-env ctx [s s-ty] [cf cf-ty] [n n-ty]]
  (let [T (set/fetch-set-type def-env ctx s-ty)]
    (list #'counted-elim-pfun-thm T s cf n)))

(defthm counted-elim-pbijective-thm
  "The second elimination rule for the [[counted]] predicate: the counted relation
must be a biject with `(range 1 n)`."
  [[T :type] [s (set T)] [cf (rel T int)] [n int]]
  (==> (counted s cf n)
       (pfun/pbijective cf s (range int/one n))))

(proof 'counted-elim-pbijective-thm
  (assume [H (counted s cf n)]
    (have <a> _ :by (p/and-elim-right H)))
  (qed <a>))

(defimplicit counted-elim-pbijective
  "The first elimination rule for the [[counted]] predicate: the counted relation
must be a biject with `(range 1 n)`the counted relation, cf. [[counted-elim-pbijective-thm]]."
  [def-env ctx [s s-ty] [cf cf-ty] [n n-ty]]
  (let [T (set/fetch-set-type def-env ctx s-ty)]
    (list #'counted-elim-pbijective-thm T s cf n)))

;; now we make the counted predicate opaque
(utils/set-opacity! #'counted-def true)

(defn decomposer-counted-type [t]
  (println "Here t=" t)
  (if (clojure.core/and (seq? t)
                        (seq t)
                        (clojure.core/= (count t) 5)
                        (clojure.core/= (first t) #'latte-finsets.core/counted-def))
    (do
      (println "(rest t)" (rest t))
      (into [] (rest t)))
    ;; XXX: cannot decompose further because
    ;; we cannot retrieve the x and y of the
    ;; definition ... add dummy witnesses ?
    (throw (ex-info "Cannot infer a counted-type" {:type t}))))

(defn decompose-counted-type [def-env ctx t]
  (utils/decomposer decomposer-counted-type def-env ctx t))

(definition finite-def
  "The definition of a finite set: `s` is finite
if the function `cf` counts the number `n` of elements in `s`,
 see [[counted]]."
  [[T :type] [s (set T)] [cf (rel T int)]]
  (exists [n int]
    (counted s cf n)))

;; Remark : the counting function must be passed
;; as a parameter because we cannot existentially
;; quantify over it... (universe issue?)

(defimplicit finite
  "The set `s` is finite according to counting function `cf`, see [[finite-def]]."
  [def-env ctx [s s-ty] [cf cf-ty]]
  (let [T (set/fetch-set-type def-env ctx s-ty)]
    (list #'finite-def T s cf)))

(defaxiom the-card-ax
  "The axiomatic definition of the cardinal number for finite sets."
  [[T :type] [s (set T)] [cf (rel T int)] [n int] [cnt (counted s cf n)]]
  int)

(defimplicit the-card
  "The cardinal number of a set counted by `cnt` of type `(counted s cf n)`,
 cf. [[counted]]."
  [def-env ctx [cnt cnt-ty]]
  (let [[T s cf n] (decompose-counted-type def-env ctx cnt-ty)]
    (list #'the-card-ax T s cf n cnt)))

(defaxiom the-card-prop-ax
  "The defining axiomatic property of the cardinal number for finite sets."
  [[T :type] [s (set T)] [cf (rel T int)] [n int] [cnt (counted s cf n)]]
  (= (the-card cnt) n))

(defimplicit the-card-prop
  "The defining property of the cardinal number of a finite set.
The `cnt` argument is a proof that the set can be counted,
 of type `(counted s cf n)`, cf. [[the-card-prop-ax]]."
  [def-env ctx [cnt cnt-ty]]
  (let [[T s cf n] (decompose-counted-type def-env ctx cnt-ty)]
    (list #'the-card-prop-ax T s cf n cnt)))


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
  (counted (set/emptyset T) cf int/zero))

(proof 'emptyset-counted
  (qed ((counted-intro (set/emptyset T) cf int/zero)
        (emptyset-pfun T int cf (range int/one int/zero))
        (p/and-intro (emptyset-pinjective T int cf (range int/one int/zero))
                     (emptyset-psurjective T cf)))))

(defthm finite-emptyset-thm
  "The emptyset of type `T` is finite, whatever the counting function."
  [[T :type] [cf (rel T int)]]
  (finite (set/emptyset T) cf))

(proof 'finite-emptyset-thm
  (qed ((q/ex-intro (lambda [k int]
                      (counted (set/emptyset T) cf k))
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

(defthm card-emptyset-thm
  [[T :type] [cf (rel T int)]]
  (= (the-card (emptyset-counted T cf)) int/zero))

(proof 'card-emptyset-thm
  (have <cnt> _ :by (emptyset-counted T cf))
  (qed (the-card-prop <cnt>)))

(defimplicit card-emptyset
  [def-env ctx [T T-ty]]
  (list #'card-emptyset-thm (list #'latte-sets.core/emptyset T) (list #'zero-count T)))







