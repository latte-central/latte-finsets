(ns latte-finsets.core
  "The formalization of finite sets.
"

  (:refer-clojure :exclude [and or not set <= < = int range = -])

  (:require [latte.core :as latte :refer [definition try-definition
                                          defthm try-defthm defaxiom defnotation
                                          forall lambda defimplicit deflemma qed
                                          assume have pose proof try-proof lambda forall]]
            [latte.utils :as utils]
            [latte-prelude.quant :as q :refer [exists]]
            [latte-prelude.prop :as p :refer [<=> and or not]]
            [latte-prelude.equal :as eq :refer [equal]]

            [latte-prelude.classic :as classic]

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
       (seteq (sa/remove (range m n) n)
              (range m (pred n)))))

(try-proof 'range-pred
  (assume [Hmn _]
    
    "Subset case"
    
    (assume [k nat
             Hk (elem k (sa/remove (range m n) n))]

      "We have to show that (<= m k) and (<= k (pred n))"

      (have <a1> (and (and (<= m k) (<= k n))
                      (not (= k n))) :by Hk)

      (have <a> (<= m k) :by (p/and-elim-left (p/and-elim-left <a1>)))

      (have <b1> (< k n) :by ((ord/lt-le-ne k n) 
                              (p/and-elim-right (p/and-elim-left <a1>))
                              (p/and-elim-right <a1>)))

      

)))
)


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
  (qed (emptyrange-emptyset)))

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
             (emptyrange-emptyset)))

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

(definition swap
  [[?T :type] [a b T]]
  (lambda [x y T]
    (p/and* (==> (equal x a) (equal y b))
            (==> (equal x b) (equal y a))
            (==> (not (equal x a)) 
                 (not (equal x b))
                 (equal y x)))))

(defthm swap-ab
  [[?T :type] [a b T]]
  ((swap a b) a b))

(proof 'swap-ab-thm
  (assume [H1 (equal a a)]
    (have <a> (equal b b) :by (eq/eq-refl b)))
  (assume [H2 (equal a b)]
    (have <b> (equal b a) :by (eq/eq-sym H2)))

  (assume [H3a (not (equal a a))
           H3b (not (equal a b))]
    (have <c1> p/absurd :by (H3a (eq/eq-refl a)))
    (have <c> (equal b a) :by (<c1> (equal b a))))

  (qed (p/and-intro* <a> <b> <c>)))

(defthm swap-ba
  [[?T :type] [a b T]]
  ((swap a b) b a))

(proof 'swap-ba-thm
  (assume [H1 (equal b a)]
    (have <a> (equal a b) :by (eq/eq-sym H1)))

  (assume [H2 (equal b b)]
    (have <b> (equal a a) :by (eq/eq-refl a)))

  (assume [H3a (not (equal b a))
           H3b (not (equal b b))]
    (have <c1> p/absurd :by (H3b (eq/eq-refl b)))
    (have <c> (equal a b) :by (<c1> (equal a b))))

  (qed (p/and-intro* <a> <b> <c>)))

(defthm swap-other
  [[?T :type] [a b T]]
  (forall [x y T]
    (==> (not (equal x a))
         (not (equal x b))
         (equal y x)
         ((swap a b) x y))))

(proof 'swap-other-thm
  (assume [x T y T
           Hneqa (not (equal x a))
           Hneqb (not (equal x b))
           Heq (equal y x)]

    (assume [H1 (equal x a)]
      (have <a1> p/absurd :by (Hneqa H1))
      (have <a> (equal y b) :by (<a1> (equal y b))))

    (assume [H2 (equal x b)]
      (have <b1> p/absurd :by (Hneqb H2))
      (have <b> (equal y a) :by (<b1> (equal y a))))

    (assume [H3a (not (equal x a))
             H3b (not (equal x b))]
      (have <c> (equal y x) :by Heq))

    (have <d> _ :by (p/and-intro* <a> <b> <c>)))

  (qed <d>))

(defthm swap-rev
  [[?T :type] [a b T]]
  (forall [x y T]
    (==> ((swap a b) x y)
         ((swap a b) y x))))

(proof 'swap-rev-thm
  (assume [x T y T
           Hswap ((swap a b) x y)]
    (have <acut> (or (equal x a) (not (equal x a)))
          :by (classic/excluded-middle-ax (equal x a)))
    (have <bcut> (or (equal x b) (not (equal x b)))
          :by (classic/excluded-middle-ax (equal x b)))

    "We proceed by case analysis"

    (assume [Heqa (equal x a)]
      
      (have <a> (equal y b)
            :by ((p/and-elim* 1 Hswap) Heqa))
      
      (have <b> ((swap a b) b a)
            :by (swap-ba a b))

      (have <c> ((swap a b) b x)
            :by (eq/eq-subst (lambda [$ T] ((swap a b) b $)) (eq/eq-sym Heqa) <b>))

      (have <d> ((swap a b) y x)
            :by (eq/eq-subst (lambda [$ T] ((swap a b) $ x)) (eq/eq-sym <a>) <c>)))

    (assume [Hneqa (not (equal x a))]
      (assume [Heqb (equal x b)]
        
        (have <e> (equal y a)
              :by ((p/and-elim* 2 Hswap) Heqb))

        (have <f> ((swap a b) a b)
              :by (swap-ab a b))

        (have <g> ((swap a b) y b)
              :by (eq/eq-subst (lambda [$ T] ((swap a b) $ b)) (eq/eq-sym <e>) <f>))

        (have <h> ((swap a b) y x)
              :by (eq/eq-subst (lambda [$ T] ((swap a b) y $)) (eq/eq-sym Heqb) <g>)))

      (assume [Hneqb (not (equal x b))]
        (have <i> (equal x y) :by (eq/eq-sym ((p/and-elim* 3 Hswap) Hneqa Hneqb)))
        (assume [Hya (equal y a)]
          (have <j1> (equal x a) :by (eq/eq-subst (lambda [$ T] (equal $ a)) (eq/eq-sym <i>) Hya))
          (have <j> p/absurd :by (Hneqa <j1>)))
        (assume [Hyb (equal y b)]
          (have <k1> (equal x b) :by (eq/eq-subst (lambda [$ T] (equal $ b)) (eq/eq-sym <i>) Hyb))
          (have <k> p/absurd :by (Hneqb <k1>)))

        (have <l> ((swap a b) y x) :by ((swap-other a b) y x <j> <k> <i>)))

      (have <m> _ :by (p/or-elim <bcut> <h> <l>)))


    (have <n> _ :by (p/or-elim <acut> <d> <m>)))

  (qed <n>))


(defthm swap-functional
  [[?T :type] [a b T] [s (set T)]]
  (pfun/functional (swap a b) s s))

(proof 'swap-functional-thm
  (assume [x T Hx (elem x s)]
    "To show: (sq/single-in s (lambda [y T] ((swap a b) x y)))"
    (assume [y1 T Hy1 (elem y1 s)
             y2 T Hy2 (elem y2 s)
             Hsw1 ((swap a b) x y1)
             Hsw2 ((swap a b) x y2)]
      "To show: (equal y1 y2)"
      (assume [Heqa (equal x a)]
        (have <a1> (equal y1 b) :by ((p/and-elim* 1 Hsw1) Heqa))
        (have <a2> (equal y2 b) :by ((p/and-elim* 1 Hsw2) Heqa))
        (have <a> (equal y1 y2) :by (eq/eq-trans <a1> (eq/eq-sym <a2>))))

      (assume [Hneqa (not (equal x a))]
        (assume [Heqb (equal x b)]
          (have <b1> (equal y1 a) :by ((p/and-elim* 2 Hsw1) Heqb))
          (have <b2> (equal y2 a) :by ((p/and-elim* 2 Hsw2) Heqb))
          (have <b> (equal y1 y2) :by (eq/eq-trans <b1> (eq/eq-sym <b2>))))

        (assume [Hneqb (not (equal x b))]
          (have <c1> (equal y1 x) :by ((p/and-elim* 3 Hsw1) Hneqa Hneqb))
          (have <c2> (equal y2 x) :by ((p/and-elim* 3 Hsw2) Hneqa Hneqb))
          (have <c> (equal y1 y2) :by (eq/eq-trans <c1> (eq/eq-sym <c2>))))

        (have <d> _ :by (p/or-elim (classic/excluded-middle-ax (equal x b)) <b> <c>)))

      (have <e> _ :by (p/or-elim (classic/excluded-middle-ax (equal x a)) <a> <d>)))

    (have <f> _ :by ((sq/single-in-intro s (lambda [y T] ((swap a b) x y)))
                     <e>)))

  (qed <f>))

(defthm swap-serial
  [[?T :type] [a b T] [s (set T)]]
  (==> (elem a s)
       (elem b s)
       (pfun/serial (swap a b) s s)))

(proof 'swap-serial-thm
  (assume [Ha (elem a s)
           Hb (elem b s)]
    (assume [x T Hx (elem x s)]
      "To show: (exists-in [y s] ((swap a b) x y))"
      (assume [Heqa (equal x a)]
        (have <a1> ((swap a b) x b)
              :by (eq/eq-subst (lambda [$ T] ((swap a b) $ b)) (eq/eq-sym Heqa) (swap-ab a b)))
        (have <a> _ :by ((sq/ex-in-intro s (lambda [$ T] ((swap a b) x $)) b) Hb <a1>)))

      (assume [Hneqa (not (equal x a))]

        (assume [Heqb (equal x b)]
          (have <b1> ((swap a b) x a)
                :by (eq/eq-subst (lambda [$ T] ((swap a b) $ a)) (eq/eq-sym Heqb) (swap-ba a b)))
          (have <b> _ :by ((sq/ex-in-intro s (lambda [$ T] ((swap a b) x $)) a) Ha <b1>)))

        (assume [Hneqb (not (equal x b))]
          (have <c1> ((swap a b) x x)
                :by ((swap-other a b) x x Hneqa Hneqb (eq/eq-refl x)))
          (have <c> _ :by ((sq/ex-in-intro s (lambda [$ T] ((swap a b) x $)) x) Hx <c1>)))

        (have <d> _ :by (p/or-elim (classic/excluded-middle-ax (equal x b)) <b> <c>)))

      (have <e> _ :by (p/or-elim (classic/excluded-middle-ax (equal x a)) <a> <d>))))

  (qed <e>))
      
(defthm swap-injective
  [[?T :type] [a b T] [s (set T)]]
  (pfun/injective (swap a b) s s))

(proof 'swap-injective-thm
  (assume [x1 T Hx1 (elem x1 s)
           x2 T Hx2 (elem x2 s)
           y1 T Hy1 (elem y1 s)
           y2 T Hy2 (elem y2 s)
           Hsw1 ((swap a b) x1 y1)
           Hsw2 ((swap a b) x2 y2)
           Heq (equal y1 y2)]
    "To show: (equal x1 x2)"
    (have <a> ((swap a b) y1 x1) :by ((swap-rev a b) x1 y1 Hsw1))
    (have <b1> ((swap a b) y2 x2) :by ((swap-rev a b) x2 y2 Hsw2))
    (have <b> ((swap a b) y1 x2) 
          :by (eq/eq-subst (lambda [$ T] ((swap a b) $ x2)) (eq/eq-sym Heq) <b1>))
    (have <c> (pfun/functional (swap a b) s s) :by (swap-functional a b s))
    (have <d> (equal x1 x2) :by ((pfun/functional-elim (swap a b) s s)
                                 <c> y1 Hy1 x1 Hx1 x2 Hx2 <a> <b>)))

  (qed <d>))

(defthm swap-injection
  [[?T :type] [a b T] [s (set T)]]
  (==> (elem a s)
       (elem b s)
       (pfun/injection (swap a b) s s)))

(proof 'swap-injection-thm
  (assume [Ha (elem a s)
           Hb (elem b s)]
    (have <a> _ :by (swap-functional a b s))
    (have <b> _ :by ((swap-serial a b s) Ha Hb))
    (have <c> _ :by (swap-injective a b s))

    (have <d> _ :by (p/and-intro* <a> <b> <c>)))

  (qed <d>))


(defthm swap-surjective
  [[?T :type] [a b T] [s (set T)]]
  (==> (elem a s)
       (elem b s)
       (pfun/surjective (swap a b) s s)))

(proof 'swap-surjective-thm
  (assume [Ha (elem a s)
           Hb (elem b s)]
    (assume [y T Hy (elem y s)]
      "We have to show: (exists-in [x s] ((swap a b) x y))"
      (have <a> (pfun/serial (swap a b) s s) :by ((swap-serial a b s) Ha Hb))
      (have <b> (exists-in [x s] ((swap a b) y x)) :by (<a> y Hy))
      (assume [x T Hx (elem x s)
               Hsw ((swap a b) y x)]
        (have <c> ((swap a b) x y) :by ((swap-rev a b) y x Hsw))
        (have <d> _ :by ((sq/ex-in-intro s (lambda [$ T] ((swap a b) $ y)) x) Hx <c>)))
      (have <e> _ :by (sq/ex-in-elim <b> <d>))))

  (qed <e>))

(defthm swap-surjection
  [[?T :type] [a b T] [s (set T)]]
  (==> (elem a s)
       (elem b s)
       (pfun/surjection (swap a b) s s)))

(proof 'swap-surjection-thm
  (assume [Ha (elem a s)
           Hb (elem b s)]
    (have <a> (pfun/functional (swap a b) s s) :by (swap-functional a b s))
    (have <b> (pfun/serial (swap a b) s s) :by ((swap-serial a b s) Ha Hb))
    (have <c> (pfun/surjective (swap a b) s s) :by ((swap-surjective a b s) Ha Hb))
    (have <d> _ :by (p/and-intro* <a> <b> <c>)))

  (qed <d>))

(defthm swap-bijective
  [[?T :type] [a b T] [s (set T)]]
  (==> (elem a s)
       (elem b s)
       (pfun/bijective (swap a b) s s)))

(proof 'swap-bijective-thm
  (assume [Ha (elem a s)
           Hb (elem b s)]
    (have <a> (pfun/injective (swap a b) s s) :by (swap-injective a b s))
    (have <b> (pfun/surjective (swap a b) s s) :by ((swap-surjective a b s) Ha Hb))
    (have <c> _ :by (p/and-intro <a> <b>)))
  (qed <c>))

(defthm swap-bijection
  [[?T :type] [a b T] [s (set T)]]
  (==> (elem a s)
       (elem b s)
       (pfun/bijection (swap a b) s s)))

(proof 'swap-bijection-thm
  (assume [Ha (elem a s)
           Hb (elem b s)]
    (have <a> (pfun/functional (swap a b) s s) :by (swap-functional a b s))
    (have <b> (pfun/serial (swap a b) s s) :by ((swap-serial a b s) Ha Hb))
    (have <c> (pfun/bijective (swap a b) s s) :by ((swap-bijective a b s) Ha Hb))
    (have <d> _ :by (p/and-intro* <a> <b> <c>)))

  (qed <d>))

(defthm swap-removal-bijection
  [[?T :type] [a b T] [s (set T)]]
  (==> (elem a s)
       (elem b s)
       (pfun/bijection (pfun/removal (swap a b) s a) (sa/remove s a) (sa/remove s b))))

(proof 'swap-removal-bijection-thm
  (assume [Ha _ Hb _]
    (have <a> _ :by ((pfun/removal-bijection (swap a b) s s a)
                     ((swap-bijection a b s) Ha Hb)
                     b Hb
                     Ha
                     (swap-ab a b))))
  (qed <a>))

(defthm rem-bijection
  [[?T :type] [f (rel T T)] [s (set T)] [a b T]]
  (==> (elem a s)
       (elem b s)
       (prel/rel-ex (lambda [g (rel T T)] 
                      (pfun/bijection g (sa/remove s a) (sa/remove s b))))))

(proof 'rem-bijection-thm
  (assume [Ha _ Hb _]
    (have <a> _ :by ((prel/rel-ex-intro (lambda [g (rel T T)] 
                                          (pfun/bijection g (sa/remove s a) (sa/remove s b)))
                                        (pfun/removal (swap a b) s a))
                     ((swap-removal-bijection a b s) Ha Hb))))
  (qed <a>))


(defthm fin-inj
  [[m n nat]]
  (==> (prel/rel-ex (lambda [g (rel nat nat)]
                      (pfun/injection g (fin m) (fin n))))
       (<= m n)))

(deflemma fin-inj-lemma [n nat]
  (forall [m nat]
    (==> (prel/rel-ex (lambda [g (rel nat nat)]
                        (pfun/injection g (fin m) (fin n))))
         (<= m n))))

(try-proof 'fin-inj-lemma
  (pose P := (lambda [m nat]
               (==> (prel/rel-ex (lambda [g (rel nat nat)]
                        (pfun/injection g (fin m) (fin n))))
                    (<= m n))))
  "We proceed by induction on m"

  "Base case m=0"
  (assume [H0 (prel/rel-ex (lambda [g (rel nat nat)]
                             (pfun/injection g (fin zero) (fin n))))]
    (have <a1> (<= zero n) :by (ord/le-zero n)))

  (have <a> (P zero) :by <a1>)

  "Inductive case"
  (assume [m nat Hind (P m)]
    (assume [Hgex (prel/rel-ex (lambda [g (rel nat nat)]
                                 (pfun/injection g (fin (succ m)) (fin n))))]

      (assume [g (rel nat nat)
               Hg (pfun/injection g (fin (succ m)) (fin n))]

        "We have to prove that (<= (succ m) n)"

        (have <b1> (<= one one) :by (ord/le-refl one))
        (have <b2> (<= one (succ m)) :by (ord/le-one m))
        (have <b> (elem one (fin (succ m)))
              :by (p/and-intro <b1> <b2>))

        (have <c1> (sq/exists-in [gone (fin n)] (g one gone))
              :by ((p/and-elim* 2 Hg) one <b>)) 

        (assume [gone nat 
                 Hgone (elem gone (fin n))
                 Hg-gone (g one gone)]

          (have <c2> (<= one gone) :by (p/and-elim-left Hgone))
          (have <c3> (<= gone n) :by (p/and-elim-right Hgone))
          (have <c4> (<= one n) :by ((ord/le-trans one gone n) <c2> <c3>)))

        (have <c> (<= one n) :by (sq/ex-in-elim <c1> <c4>))
        
        )
      )
    )
  )
