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
            [latte-sets.ralgebra :as ra]
            [latte-sets.powerrel :as prel]
            [latte-sets.pfun :as pfun]
                       
            [latte-nats.core :as nat :refer [zero one succ nat = <>]]
            [latte-nats.ord :as natord :refer [< <=]]

            [latte-finsets.range :as r :refer [range]]
            [latte-finsets.finite :as f :refer [finite]]
            
            ))




;; from: https://www.math.drexel.edu/~tolya/pigeonhole
(defthm pigeonhole
  [[k nat] [m nat]]
  (==> (prel/rel-ex (lambda [f (rel nat nat)]
                      (pfun/injective f (range one k) (range one m))))
       (<= k m)))

(try-proof 'pigeonhole
  (pose P := (lambda [k nat] (==> (prel/rel-ex (lambda [f (rel nat nat)]
                                                 (pfun/injective f (range one k) (range one m))))
                                  (<= k m))))
  "The proof is by induction on k"
  "The base case is trivial"
  (assume [Hrel (prel/rel-ex (lambda [f (rel nat nat)]
                               (pfun/injective f (range one zero) (range one m))))]
    "The conclusion is reachable directly"
    (have <a1> (<= zero m) :by (natord/le-zero m)))
  (have <a> (P zero) :by <a1>)

  "Now, the inductive case"
  (assume [k nat
           Hk (P k)]
    "We have to show (P (succ k))"
    (assume [Hrel (prel/rel-ex (lambda [f (rel nat nat)]
                                 (pfun/injective f (range one (succ k)) (range one m))))]
      "We use existential elimination"
      (assume [f (rel nat nat)
               Hf (pfun/injective f (range one (succ k)) (range one m))]

        "We have to show (<= (succ k) m)"
        (have <hrel> (==> (prel/rel-ex (lambda [f (rel nat nat)]
                                         (pfun/injective f (range one k) (range one m))))
                          (<= k m)) :by Hk)

        

      ))))



(comment
(defthm card-inf-inj-lemma 
  [[f (rel nat nat)] [n nat] [m nat]]
  (==> (< n2 n1)
       (forall [f (rel nat nat)] (not (pfun/injective f (range one n1) (range one n2))))))

(try-proof 'card-inf-inj-lemma
  (assume [Hinf (< n2 n1)]
    (assume [f (rel nat nat)
             Hf (pfun/injective f (range one n1) (range one n2))]
      (have <finj> (forall-in [i1 (range one n1)]
                     (forall-in [i2 (range one n1)]
                       (forall-in [j1 (range one n2)]
                         (forall-in [j2 (range one n2)]
                           (==> (f i1 j1)
                                (f i2 j2)
                                (not (equal i1 i2))
                                (not (equal j1 j2))))))) 
            :by ((pfun/injective-contra f (range one n1) (range one n2)) Hf))
      "We have to derive a countradiction"
      (assume [i1 nat Hi1 (elem i1 (range one n1))
               i2 nat Hi2 (elem i2 (range one n1))
               j1 nat Hj1 (elem j1 (range one n2))
               j2 nat Hj2 (elem j2 (range one n2))]
        (assume [Hf1 (f i1 j1)
                 Hf2 (f i2 j2)
                 Hneqj (not (equal i1 i2))]
          (have <neqi> (not (equal j1 j2)) :by (<finj> i1 Hi1 i2 Hi2 j1 Hj1 j2 Hj2 Hf1 Hf2 Hneqj))
)))))
)

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
        (have <h1> (pfun/bijection f1 (range one n1) s) :by Hf1)
        (have <h2> (pfun/bijection f2 (range one n2) s) :by Hf2)
        (pose rf2 := (ra/rinverse f2))
        (have <h2r>  (pfun/bijection rf2 s (range one n2)) 
              :by (pfun/bijection-inverse-bijection f2 (range one n2) s <h2>))
        
        ;; We pose  g = (pfcomp-mid r1 rf2 (range one n1) s (range one n2))
        (pose g := (pfun/pfcomp-mid f1 rf2 (range one n1) s (range one n2)))

        ;; step1: we have to show (bijection g (range one n1) (range one n2))
        (have <step1> (pfun/bijection g (range one n1) (range one n2))
              :by ((pfun/pfcomp-bijection-mid f1 rf2 (range one n1) s (range one n2))
                   <h1> <h2r>))

        ;; step3: we need a lemma to thow that if  (< n1 n2) then there is no injection from (range one n1) to (range one n2)

        ;; step4: since g is a bijection from (range one n1) to (range one n2)
        ;; it is also an injection from (range one n1) to (range one n2)
        ;; hence we have a contradiction wiz. our injection lemma

        ;; step4: there is also a contradiction if (< n2 n1)
        
        ;; step5: we conclude (= n1 n2)
      )

)))
