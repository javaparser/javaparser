(set-option :produce-unsat-cores true)
(set-option :produce-models true)
(set-logic ALL)

(declare-sort T 0)
(declare-sort U 0)

(declare-fun instanceof (U T) Bool)
(declare-fun exactinstanceof (U T) Bool)
(declare-fun subtype (T T) Bool)
(declare-fun typeof (U) T)

(assert (forall ((t1 T)) (subtype t1 t1)))
(assert (forall ((t1 T) (t2 T)) (! (=> (and (subtype t1 t2) (subtype t2 t1)) (= t1 t2)) :pattern ((subtype t1 t2) (subtype t2 t1)))))
(assert (forall ((t1 T) (t2 T) (t3 T)) (! (=> (and (subtype t1 t2) (subtype t2 t3)) (subtype t1 t3)) :pattern ((subtype t1 t2) (subtype t2 t3)))))
(assert (forall ((u U) (t T)) (! (= (instanceof u t) (subtype (typeof u) t)) :pattern ((instanceof u t)))))
(assert (forall ((u U) (t T)) (! (= (exactinstanceof u t) (= (typeof u) t)) :pattern ((exactinstanceof u t)))))

;; Integer
(declare-fun u2i (U) Int)
(declare-fun i2u (Int) U)
(declare-const sort_int T)

(assert (forall ((i Int)) (= (u2i (i2u i)) i)))
(assert (forall ((x U)) (! (=> (= (typeof x) sort_int)  (= (i2u (u2i x)) x)) :pattern ((typeof x)))))
(assert (forall ((t T)) (! (=> (subtype t sort_int) (= t sort_int)) :pattern ((subtype t sort_int)))))
; (assert (forall ((x U)) (! (=> (instanceof x sort_int)  (= (typeof x ) sort_int)) :pattern ((instanceof x sort_int)))))
(assert (forall ((i Int)) (! (= (typeof (i2u i)) sort_int) :pattern ((i2u i)))))

(declare-fun u2b (U) Bool)
(declare-fun b2u (Bool) U)
(declare-const sort_boolean T)

(assert (instanceof (b2u true) sort_boolean))
(assert (instanceof (b2u false) sort_boolean))
(assert (forall ((b Bool)) (= (u2b (b2u b)) b)))
; This seems to improve Z3 performance: Needs investigation (probably triggers above)
(assert (not (u2b (b2u false))))
(assert (forall ((u U)) (! (=> (= (typeof u) sort_boolean) (or (= u (b2u true)) (= u (b2u false)))) :pattern ((typeof u)))))
(assert (forall ((x U)) (! (=> (instanceof x sort_boolean)  (= (typeof x ) sort_boolean)) :pattern ((instanceof x sort_boolean)))))

(declare-fun cast (U T) U)
(assert (forall ((x U) (t T)) (! (subtype (typeof (cast x t)) t) :pattern ((cast x t)))))
(assert (forall ((x U) (t T)) (! (=> (subtype (typeof x) t) (= (cast x t) x)) :pattern ((cast x t)))))


(declare-fun u2f (U) Float32)
(declare-fun f2u (Float32) U)
;(declare-const sort_float T)

(declare-fun u2d (U) Float64)
(declare-fun d2u (Float64) U)
;(declare-const sort_double T)
(assert (forall ((f Float32)) (= (u2f (f2u f)) f)))
(assert (forall ((x U)) (=> (= (typeof x) sort_float) (= (f2u (u2f x)) x))))
(assert (forall ((x U)) (=> (instanceof x sort_float) (= (typeof x ) sort_float))))
(assert (forall ((f Float32)) (= (typeof (f2u f)) sort_float)))

(assert (forall ((d Float64)) (= (u2d (d2u d)) d)))
(assert (forall ((x U)) (=> (= (typeof x) sort_double) (= (d2u (u2d x)) x))))
(assert (forall ((x U)) (=> (instanceof x sort_double) (= (typeof x ) sort_double))))
(assert (forall ((d Float64)) (= (typeof (d2u d)) sort_double)))
