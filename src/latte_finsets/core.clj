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
                       
            [latte-integers.core :as int :refer [int = zero one]]
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

(defthm range-eq
  [[m int] [n int]]
  (==> (= m n)
       (forall [k int]
         (==> (elem k (range m n))
              (= k n)))))

(proof 'range-eq
  (assume [Heq (= m n)
           k int
           Hk (elem k (range m n))]
    (have <a> (elem k (range n n))
          :by (eq/eq-subst (lambda [i int]
                             (elem k (range i n))) Heq Hk))
    (have <b> (<= n k) :by (p/and-elim-left <a>))
    (have <c> (<= k n) :by (p/and-elim-right <a>))
    (have <d> (= k n) :by (eq/eq-sym ((ord/le-antisym n k) <b> <c>))))
  (qed <d>))

(defthm range-one
  [[n int]]
  (forall-in [k int (range n n)]
    (= k n)))

(proof 'range-one
  (have <a> (= n n) :by (eq/eq-refl n))
  (qed  ((range-eq n n) <a>)))

(definition counted-def
  "The set `s` is counted from 1 to `n`"
  [[T :type] [s (set T)] [cf (rel T int)] [n int]]
  (and (pfun cf s (range one n))
       (pfun/pbijective cf s (range one n))))

(defimplicit counted
  "The set `s` is counted from 1 to `n`, cf. [[counted-def]]"
  [def-env ctx [s s-ty] [cf cf-ty] [n n-ty]]
  (let [[T _] (rel/fetch-rel-type def-env ctx cf-ty)]
    (list #'counted-def T s cf n)))

;; since we want `counted` to be opaque we need introduction and eliminations rules.

(defthm counted-intro-thm
  "The introduction rule for the counted predicate."
  [[T :type] [s (set T)] [cf (rel T int)] [n int]]
  (==> (pfun cf s (range one n))
       (pfun/pbijective cf s (range one n))
       (counted s cf n)))

(proof 'counted-intro-thm
  (assume [H1 (pfun cf s (range one n))
           H2 (pfun/pbijective cf s (range one n))]
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
       (pfun cf s (range one n))))

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
       (pfun/pbijective cf s (range one n))))

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
  (if (clojure.core/and (seq? t)
                        (seq t)
                        (clojure.core/= (count t) 5)
                        (clojure.core/= (first t) #'latte-finsets.core/counted-def))
    (do
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
  (pfun/psurjective cf (set/emptyset T) (range one zero)))

(proof 'emptyset-psurjective
  (assume [y int
           Hy (elem y (range one zero))]
    (have <a> (< zero one) :by (ord/lt-succ zero))
    (have <b> (not (elem y (range one zero)))
          :by ((range-empty one zero)
               <a> y))
    (have <c> p/absurd :by (<b> Hy))
    (have <d> _ :by (<c> (exists-in [x T (set/emptyset T)]
                           (cf x y)))))
  (qed <d>))

(deflemma emptyset-counted
  [[T :type] [cf (rel T int)]]
  (counted (set/emptyset T) cf zero))

(proof 'emptyset-counted
  (qed ((counted-intro (set/emptyset T) cf zero)
        (emptyset-pfun T int cf (range one zero))
        (p/and-intro (emptyset-pinjective T int cf (range one zero))
                     (emptyset-psurjective T cf)))))

(defthm finite-emptyset-thm
  "The emptyset of type `T` is finite, whatever the counting function."
  [[T :type] [cf (rel T int)]]
  (finite (set/emptyset T) cf))

(proof 'finite-emptyset-thm
  (qed ((q/ex-intro (lambda [k int]
                      (counted (set/emptyset T) cf k))
                    zero)
        (emptyset-counted T cf))))

(definition zero-count
  "This is a dummy counting function for use in [[finite-emptyset]]."
  [[T :type]]
  (lambda [x T]
    (lambda [k int]
      (= k zero))))

(definition finite-emptyset
  "The emptyset is finite."
  [[T :type]]
  (finite-emptyset-thm T (zero-count T)))

(defthm card-emptyset-thm
  [[T :type] [cf (rel T int)]]
  (= (the-card (emptyset-counted T cf)) zero))

(proof 'card-emptyset-thm
  (have <cnt> _ :by (emptyset-counted T cf))
  (qed (the-card-prop <cnt>)))

(definition card-emptyset
  "The cardinal of the emptyset is zero."
  [[T :type]]
  (card-emptyset-thm T (zero-count T)))

;; singletons

(definition singleton-def
  "The singleton set `{x}`."
  [[T :type] [x T]]
  (lambda [y T] (equal x y)))

(defimplicit singleton
  "The singleton set `{x}`, cf. [[singleton-def]]."
  [def-env ctx [x x-ty]]
  (list #'singleton-def x-ty x))

(defthm singleton-thm
  [[T :type] [x T]]
  (elem x (singleton x)))

(proof 'singleton-thm
  (qed (eq/eq-refl x)))

(definition one-count
  "The counting relation for singletons."
  [[T :type]]
  (lambda [x T]
    (lambda [k int]
      (= k one))))

(deflemma singleton-pfun
  [[T :type] [x T]]
  (pfun/pfun (one-count T) (singleton x) (range one one)))

(proof 'singleton-pfun
  (assume [z T
           Hx (elem z (singleton x))]
    (assume [y1 int
             Hy1 (elem y1 (range one one))]
      (have <a> (= y1 one) :by ((range-one one) y1 Hy1))
      (assume [y2 int
               Hy2 (elem y2 (range one one))]
        (have <b> (= y2 one) :by ((range-one one) y2 Hy2))
        (assume [Hf1 ((one-count T) x y1)
                 Hf2 ((one-count T) x y2)]
          (have <c> (= y1 y2) :by (eq/eq-trans <a> (eq/eq-sym <b>)))))))
  (qed <c>))

(deflemma singleton-pinjective
  [[T :type] [x T]]
  (pfun/pinjective (one-count T) (singleton x) (range one one)))

(proof 'singleton-pinjective
  (assume [x1 T
           Hx1 (elem x1 (singleton x))]
    (have <a> (equal x x1) :by Hx1)
    (assume [x2 T
             Hx2 (elem x2 (singleton x))]
      (have <b> (equal x x2) :by Hx2)
      (assume [y1 int
               Hy1 (elem y1 (range one one))
               y2 int
               Hy2 (elem y2 (range one one))
               Hf1 ((one-count T) x1 y1)
               Hf2 ((one-count T) x2 y2)
               Hyeq (= y1 y2)]
        (have <c> (equal x1 x2) :by (eq/eq-trans (eq/eq-sym <a>) <b>)))))
  (qed <c>))

(deflemma singleton-psurjective
  [[T :type] [x T]]
  (pfun/psurjective (one-count T) (singleton x) (range one one)))

(proof 'singleton-psurjective
  (assume [y int
           Hy (elem y (range one one))]
    (have <a> (elem x (singleton x)) :by (singleton-thm T x))
    (have <b> (= y one) :by ((range-one one) y Hy))
    (have <c> ((one-count T) x y) :by <b>)
    (have <e> _ :by ((q/ex-intro (lambda [z T]
                                   (and (elem z (singleton x))
                                        ((one-count T) z y))) x)
                     (p/and-intro <a> <c>))))
  (qed <e>))

(deflemma singleton-counted
  [[T :type] [x T]]
  (counted (singleton x) (one-count T) one))

(proof 'singleton-counted
  (qed ((counted-intro (singleton x) (one-count T) one)
        (singleton-pfun T x)
        (p/and-intro (singleton-pinjective T x)
                     (singleton-psurjective T x)))))

(defthm finite-singleton
  "The emptyset of type `T` is finite, whatever the counting function."
  [[T :type] [x T]]
  (finite (singleton x) (one-count T)))

(proof 'finite-singleton
  (have <a> (counted (singleton x) (one-count T) one) :by (singleton-counted T x))
  (qed ((q/ex-intro (lambda [k int]
                      (counted (singleton x) (one-count T) k)) one)
        <a>)))


(definition the-card-singleton
  "The cardinal of the singleton set `{x}`."
  [[T :type] [x T]]
  (the-card (singleton-counted T x)))

(defthm the-card-singleton-prop
  "The cardinal of a singleton is `one`."
  [[T :type] [x T]]
  (= (the-card-singleton T x) one))

(proof 'the-card-singleton-prop
  (qed (the-card-prop (singleton-counted T x))))




