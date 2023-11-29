(ns latte-finsets.core
  "The formalization of finite sets.
"

  (:refer-clojure :exclude [and or not set <= < = int range =])

  (:require [latte.core :as latte :refer [definition try-definition
                                          defthm defaxiom defnotation
                                          forall lambda defimplicit deflemma qed
                                          assume have pose proof try-proof lambda forall]]
            [latte.utils :as utils]
            [latte-prelude.quant :as q :refer [exists]]
            [latte-prelude.prop :as p :refer [<=> and or not]]
            [latte-prelude.equal :as eq :refer [equal]]

            [latte-prelude.classic :as classic]

            [latte-sets.set :as set :refer [set elem subset seteq]]
            [latte-sets.quant :as sq :refer [forall-in exists-in]]
            [latte-sets.rel :as rel :refer [rel]]
            [latte-sets.powerrel :as prel]
            [latte-sets.pfun :as pfun]
                       
            [latte-nats.core :as nat :refer [zero one succ nat =]]
            [latte-nats.ord :as ord :refer [< <=]]))

(definition range
  "The range set from `m` to `n` (inclusive)."
  [[m nat] [n nat]]
  (lambda [k nat]
    (and (<= m k)
         (<= k n))))

(defthm range-empty
  [[m nat] [n nat]]
  (==> (< n m)
       (forall [k nat] (not (elem k (range m n))))))

(proof 'range-empty
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

(defthm range-eq
  [[m nat] [n nat]]
  (==> (= m n)
       (forall [k nat]
         (==> (elem k (range m n))
              (= k n)))))

(proof 'range-eq
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
  (qed  ((range-eq n n) <a>)))

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

(defthm finite-card-single
  [[?T :type] [s (set T)]]
  (forall [n1 n2 nat]
    (==> (prel/rel-ex (lambda [f1 (rel T nat)]
                        (finite-prop s n1 f1)))
         (prel/rel-ex (lambda [f2 (rel T nat)]
                        (finite-prop s n2 f2)))
         (= n1 n2))))

(try-proof 'finite-card-single-thm
  (assume [n1 _
           n2 _
           Hn1 _
           Hn2 _]
    (assume [f1 (rel T nat)
             Hf1 (finite-prop s n1 f1)]
      (assume [f2 (rel T nat)
               Hf2 (finite-prop s n2 f2)]
        "We proceed by contradiction."
        (assume [Hneq (not (= n1 n2))]
          (exists 
        
    ))))



(deflemma card-single-prop
  [[T :type] [s (set T)] [n1 int] [n2 int] [f (rel T int)]]
  (==> (finite-prop T s n1 f)
       (finite-prop T s n2 f)
       (= n1 n2)))

(proof 'card-single-prop
  (assume [Hf1 _ Hf2 _]
    (have <H1-1> (forall-in [x s]
                   (forall-in [k1 (range one n1)]
                     (forall-in [k2 (range one n1)]
                       (==> (f x k1)
                            (f x k2)
                            (= k1 k2)))))
          :by (p/and-elim-left Hf1))
    (have <H1-2> (forall-in [x s]
                   (forall-in [k1 (range one n2)]
                     (forall-in [k2 (range one n2)]
                       (==> (f x k1)
                            (f x k2)
                            (= k1 k2)))))
          :by (p/and-elim-left Hf2))
    (have <H2-1> ())))

;; the emptyset case

(deflemma emptyset-pfun
  [[T :type] [U :type] [f (rel T U)] [to (set U)]]
  (pfun f (set/emptyset T) to))

(proof 'emptyset-pfun
  (assume [x T
           Hx (elem x (set/emptyset T))]
    (have <a> p/absurd :by Hx)
    (have <b> _ :by (Hx (forall-in [y1 to]
                                   (forall-in [y2 to]
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
    (have <b> _ :by (Hx1 (forall-in [x2 (set/emptyset T)]
                           (forall-in [y1 to]
                             (forall-in [y2 to]
                               (==> (f x1 y1)
                                    (f x2 y2)
                                    (equal y1 y2)
                                    (equal x1 x2))))))))
  (qed <b>))

(deflemma emptyset-psurjective
  [[T :type] [f (rel T int)]]
  (pfun/psurjective f (set/emptyset T) (range one zero)))

(proof 'emptyset-psurjective
  (assume [y int
           Hy (elem y (range one zero))]
    (have <a> (< zero one) :by (ord/lt-succ zero))
    (have <b> (not (elem y (range one zero)))
          :by ((range-empty one zero)
               <a> y))
    (have <c> p/absurd :by (<b> Hy))
    (have <d> _ :by (<c> (exists-in [x (set/emptyset T)]
                           (f x y)))))
  (qed <d>))


(deflemma finite-emptyset-prop
  [[T :type]]
  (finite-prop T (set/emptyset T) zero (rel/emptyrel T int)))

(proof 'finite-emptyset-prop
  (pose f := (rel/emptyrel T int))
  (pose from := (set/emptyset T))
  (pose to := (range one zero))
  (have <a> (pfun f from to)
        :by (emptyset-pfun T int f to))
  (have <b> (pfun/pbijective f from to)
        :by (p/and-intro (emptyset-pinjective T int f to)
                         (emptyset-psurjective T f)))
  (qed (p/and-intro <a> <b>)))

(defthm finite-emptyset
  "The emptyset of type `T` is finite."
  [[T :type]]
  (finite (set/emptyset T)))

(proof 'finite-emptyset
  (pose R := (rel/emptyrel T int))
  (have <a> (finite-prop T (set/emptyset T) zero R) 
        :by (finite-emptyset-prop T))
  (have <b> _
    :by ((prel/rel-ex-intro (lambda [f (rel T int)] 
                              (finite-prop T (set/emptyset T) zero f)) R)
         <a>))
  (have <c> _ :by ((q/ex-intro (lambda [n int] 
                                 (prel/rel-ex (lambda [f (rel T int)] 
                                                (finite-prop T (set/emptyset T) n f)))) zero)
                   <b>))
  (qed <c>))

;; >>>>>>> TODO : not yet updated <<<<<<<<<

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


(definition insert-def
  "Insertion of element `x` in set `s`."
  [[T :type] [x T] [s (set T)]]
  (lambda [y T]
    (or (equal y x)
        (elem y s))))

(defimplicit insert
  "Insertion of element `x` in set `s`, cf. [[insert-def]]."
  [def-env ctx [x T] [s s-ty]]
  (list #'insert-def T x s))

(defthm insert-prop-elem
  [[T :type] [x T] [s (set T)]]
  (elem x (insert x s)))

(proof 'insert-prop-elem
  (have <a> (equal x x) :by (eq/eq-refl x))
  (qed (p/or-intro-left <a> (elem x s))))

(defthm insert-prop-set
  [[T :type] [x T] [s (set T)]]
  (forall [y T]
    (==> (elem y s)
         (elem y (insert x s))))) ;;; XXX : rewrite with subset

(proof 'insert-prop-set
  (assume [y T
           Hy (elem y s)]
    (have <a> _ :by (p/or-intro-right (equal y x) Hy)))
  (qed <a>))

(defthm insert-prop-neq
  [[T :type] [x T] [s (set T)]]
  (forall [y T]
    (==> (elem y (insert x s))
         (not (equal y x))
         (elem y s))))

(proof 'insert-prop-neq
  (assume [y T
           H1y (elem y (insert x s))
           H2y (not (equal y x))]
    (assume [H1 (equal y x)]
      (have <a1> p/absurd :by (H2y H1))
      (have <a> (elem y s) :by (<a1> (elem y s))))
    (assume [H2 (elem y s)]
      (have <b> (elem y s) :by H2))
    (have <c> (elem y s)
          :by (p/or-elim H1y (elem y s) <a> <b>)))
  (qed <c>))

(defthm insert-prop-idem
  [[T :type] [x T] [s (set T)]]
  (==> (elem x s)
       (seteq s (insert x s))))

(proof 'insert-prop-idem
  (assume [Hx (elem x s)]
    "First the subset case."
    (assume [y T
             Hy (elem y s)]
      (have <a1> (elem y (insert x s)) :by ((insert-prop-set T x s) y Hy)))
    (have <a> (subset s (insert x s)) :by <a1>)
    "Second the supset case."
    (assume [y T
             Hy (elem y (insert x s))]
      "We use classical reasoning."
      (assume [Hyes (equal y x)]
        (have <b> (elem y s) :by (eq/eq-subst (lambda [z T]
                                                (elem z s))
                                              (eq/eq-sym Hyes)
                                              Hx)))
      (assume [Hno (not (equal y x))]
        (have <c> (elem y s) :by ((insert-prop-neq T x s)
                                  y Hy Hno)))
      (have <d> (or (equal y x)
                    (not (equal y x))) :by (classic/excluded-middle-ax (equal y x)))
      (have <e> (elem y s) :by (p/or-elim <d> (elem y s) <b> <c>)))
    (have <f> (subset (insert x s) s) :by <e>)
    (have <g> _ :by (p/and-intro <a> <f>)))
  (qed <g>))

(definition insert-count
  [[T :type] [s (set T)] [size int]]
  (lambda [y T]
    (lambda [k int]
      (and (==> (elem y s) (= k size))
           (==> (not (elem y s)) (= k (succ size)))))))

(deflemma insert-pfun-elem
  [[T :type] [x T] [s (set T)] [size int]]
  (==> (elem x s)
       (pfun/pfun (insert-count T s size)  (insert x s) (range one size))))

(proof 'insert-pfun-elem
  (assume [Hx (elem x s)
           z T
           Hz (elem z (insert x s))]
    (have <a1> (seteq s (insert x s)) :by ((insert-prop-idem T x s) Hx))
    (have <a2> (set/set-equal s (insert x s))
          :by ((set/seteq-implies-set-equal-ax T s (insert x s)) <a1>))
    (have <a3> (<=> (elem z s)  ;;; XXX : define a substitution law for set-equal
                                ;;;       also congruence
                    (elem z (insert x s)))
          :by (<a2> (lambda [w (set T)]
                      (elem z w))))
    (have <a> (elem z s) :by ((p/and-elim-right <a3>) Hz))
    (assume [y1 int
             Hy1 (elem y1 (range one size))
             y2 int
             Hy2 (elem y2 (range one size))
             Hcount1 ((insert-count T s size) z y1)
             Hcount2 ((insert-count T s size) z y2)]
      (have <b> (= y1 size) :by ((p/and-elim-left Hcount1) <a>))
      (have <c> (= y2 size) :by ((p/and-elim-left Hcount2) <a>))
      (have <d> (= y1 y2) :by (eq/eq-trans <b> (eq/eq-sym <c>)))))
  (qed <d>))


(comment

  (deflemma insert-count-not-elem
    [[T :type] [s (set T)] [size int] [x T] [k int]]
    (==> (not (elem x s))
         ((insert-count T s size) x k)
         (= k (succ size))))

  (proof 'insert-count-not-elem
    (assume [Hx (not (elem x s))
             Hcount ((insert-count T s size) x k)]
      (have <a> (==> (not (elem x s))
                     (= k (succ size))) :by (p/and-elim-right Hcount))
      (have <b> (= k (succ size)) :by (<a> Hx)))
    (qed <b>))

  (deflemma insert-pfun-not-elem
    [[T :type] [x T] [s (set T)] [size int]]
    (==> (not (elem x s))
         (pfun/pfun (insert-count T s size)  (insert x s) (range one (succ size)))))

  (proof 'insert-pfun-not-elem
    (assume [Hx (not (elem x s))
             z T
             Hz (elem z (insert x s))]
      (assume [y1 int
               Hy1 (elem y1 (range one (succ size)))]
        (have <a> (= y1 (succ size)) :by ((insert-count-not-elem T s size z)))
        (assume [y2 int
                 Hy2 (elem y2 (range one size))])))))
