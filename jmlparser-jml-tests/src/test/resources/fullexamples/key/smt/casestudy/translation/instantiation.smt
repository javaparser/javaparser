; BIT_HEAP (_ BitVec 2)
; BIT_OBJECT (_ BitVec 5)
; BIT_INT (_ BitVec 3)
; BIT_FIELD (_ BitVec 4)
(set-option :print-success true)

(set-option :produce-unsat-cores true)

(set-option :produce-models true)

(set-option :produce-proofs true)

          ; Declaration of sorts.

(declare-sort u 0)
          ; Predicates used in formula:


(declare-fun wellFormed_12
 ((_ BitVec 2) ) Bool )
          ; Types expressed by predicates:


(declare-fun type_of_SumAndMax_13_14
 ((_ BitVec 5) ) Bool )

(declare-fun type_of_Null_36_37
 ((_ BitVec 5) ) Bool )

(declare-fun type_of_any_23_24
 ((_ BitVec 5) ) Bool )

(declare-fun type_of_Heap_9_10
 ((_ BitVec 2) ) Bool )

(declare-fun type_of_int_5_6
 ((_ BitVec 3) ) Bool )

(declare-fun type_of_java_dot_lang_dot_Object_3_4
 ((_ BitVec 5) ) Bool )

(declare-fun type_of_int_Array_0_1
 ((_ BitVec 5) ) Bool )

(declare-fun type_of_boolean_19_20
 ((_ BitVec 5) ) Bool )

(declare-fun type_of_Field_16_17
 ((_ BitVec 4) ) Bool )

          ; Function declarations

(declare-fun heap_11
 () (_ BitVec 2) )

(declare-fun dummy_Field_46
 () (_ BitVec 4) )

(declare-fun dummy_java_dot_lang_dot_Object_43
 () (_ BitVec 5) )

(declare-fun dummy_boolean_45
 () (_ BitVec 5) )

(declare-fun k_0_8
 () (_ BitVec 3) )

(declare-fun i_33
 () (_ BitVec 3) )

(declare-fun length_7
 ((_ BitVec 5) ) (_ BitVec 3) )

(declare-fun self_15
 () (_ BitVec 5) )

(declare-fun dummy_Heap_41
 () (_ BitVec 2) )

(declare-fun boolean_col__col_select_21
 ((_ BitVec 2) (_ BitVec 5) (_ BitVec 4)  ) (_ BitVec 5) )

(declare-fun a_2
 () (_ BitVec 5) )

(declare-fun dummy_any_40
 () (_ BitVec 5) )

(declare-fun bsum_34
 ((_ BitVec 3) (_ BitVec 3) (_ BitVec 3) ) (_ BitVec 3) )

(declare-fun anon_heap_loop_29
 () (_ BitVec 2) )

(declare-fun dummy_int_Array_44
 () (_ BitVec 5) )

(declare-fun null
 () (_ BitVec 5) )

(declare-fun java_dot_lang_dot_Object_col__col__abo_created_abc__18
 () (_ BitVec 4) )

(declare-fun dummy_SumAndMax_38
 () (_ BitVec 5) )

(declare-fun SumAndMax_col__col__dollar_max_31
 () (_ BitVec 4) )

(declare-fun arr_27
 ((_ BitVec 3) ) (_ BitVec 4) )

(declare-fun SumAndMax_col__col_exactInstance_25
 ((_ BitVec 5) ) (_ BitVec 5) )

(declare-fun dummy_Null_39
 () (_ BitVec 5) )

(declare-fun SumAndMax_col__col__dollar_sum_35
 () (_ BitVec 4) )

(declare-fun int_col__col_select_28
 ((_ BitVec 2) (_ BitVec 5) (_ BitVec 4) ) (_ BitVec 3) )

(declare-fun TRUE_22
 () (_ BitVec 5) )

(declare-fun dummy_int_42
 () (_ BitVec 3) )

(assert
 (not

  (=>
   (and

          ; Assumptions for function definitions:

    (type_of_Heap_9_10 heap_11 )

    (type_of_Field_16_17 dummy_Field_46 )

    (type_of_java_dot_lang_dot_Object_3_4 dummy_java_dot_lang_dot_Object_43 )

    (type_of_boolean_19_20 dummy_boolean_45 )

    (type_of_SumAndMax_13_14 self_15 )

    (type_of_Heap_9_10 dummy_Heap_41 )

    (forall
     (
      (tvar_47 (_ BitVec 2)))
     (forall
      (
       (tvar_48 (_ BitVec 5)))
      (forall
       (
        (tvar_49 (_ BitVec 4)))
       (=>
        (and
         (and
          (type_of_Heap_9_10 tvar_47 )
          (type_of_java_dot_lang_dot_Object_3_4 tvar_48 ) )
         (type_of_Field_16_17 tvar_49 ) )
        (type_of_boolean_19_20
         (boolean_col__col_select_21 tvar_47 tvar_48 tvar_49 ) ) ))))

    (type_of_int_Array_0_1 a_2 )

    (type_of_any_23_24 dummy_any_40 )

    (type_of_Heap_9_10 anon_heap_loop_29 )

    (type_of_int_Array_0_1 dummy_int_Array_44 )

    (type_of_Null_36_37 null )

    (type_of_Field_16_17 java_dot_lang_dot_Object_col__col__abo_created_abc__18 )

    (type_of_SumAndMax_13_14 dummy_SumAndMax_38 )

    (type_of_Field_16_17 SumAndMax_col__col__dollar_max_31 )

    (forall
     (
      (tvar_50 (_ BitVec 3)))
     (type_of_Field_16_17
      (arr_27 tvar_50 ) ))

    (forall
     (
      (tvar_51 (_ BitVec 5)))
     (=>
      (type_of_any_23_24 tvar_51 )
      (type_of_boolean_19_20
       (SumAndMax_col__col_exactInstance_25 tvar_51 ) ) ))

    (type_of_Null_36_37 dummy_Null_39 )

    (type_of_Field_16_17 SumAndMax_col__col__dollar_sum_35 )

    (type_of_boolean_19_20 TRUE_22 )

          ; Assumptions for type hierarchy:

    (forall
     (
      (tvar2_52 (_ BitVec 5)))
     (=>
      (type_of_SumAndMax_13_14 tvar2_52 )
      (type_of_java_dot_lang_dot_Object_3_4 tvar2_52 ) ))

    (type_of_SumAndMax_13_14 null )

    (type_of_any_23_24 null )

    (type_of_java_dot_lang_dot_Object_3_4 null )

    (type_of_int_Array_0_1 null )


    ; do not model this relation.	
    ;(forall
    ; (
    ;  (tvar2_53 u))
    ; (=>
    ;  (type_of_Heap_9_10 tvar2_53 )
    ;  (type_of_any_23_24 tvar2_53 ) ))

    ; do not model this relation
    ;(forall
    ; (
    ;  (tvar2_54 u))
    ; (=>
    ;  (type_of_int_5_6 tvar2_54 )
    ;  (type_of_any_23_24 tvar2_54 ) ))

    (forall
     (
      (tvar2_55 (_ BitVec 5)))
     (=>
      (type_of_java_dot_lang_dot_Object_3_4 tvar2_55 )
      (type_of_any_23_24 tvar2_55 ) ))

    (forall
     (
      (tvar2_56 (_ BitVec 5)))
     (=>
      (type_of_int_Array_0_1 tvar2_56 )
      (type_of_java_dot_lang_dot_Object_3_4 tvar2_56 ) ))

    (forall
     (
      (tvar2_57 (_ BitVec 5)))
     (=>
      (type_of_boolean_19_20 tvar2_57 )
      (type_of_any_23_24 tvar2_57 ) ))

    ; do not model this relation
    ;(forall
    ; (
    ;  (tvar2_58 u))
    ; (=>
    ;  (type_of_Field_16_17 tvar2_58 )
    ;  (type_of_any_23_24 tvar2_58 ) ))

          ; Assumptions for uniqueness of functions:

    (and
     (and
      (and
       (and true
        (forall
         (
          (n0_59 (_ BitVec 3)))
         (not
          (= java_dot_lang_dot_Object_col__col__abo_created_abc__18
           (arr_27 n0_59 ) ) )) )
       (not
        (= java_dot_lang_dot_Object_col__col__abo_created_abc__18 SumAndMax_col__col__dollar_max_31 ) ) )
      (not
       (= java_dot_lang_dot_Object_col__col__abo_created_abc__18 SumAndMax_col__col__dollar_sum_35 ) ) ) true )

    (and
     (and
      (and true
       (forall
        (
         (n0_60 (_ BitVec 3)))
        (not
         (=
          (arr_27 n0_60 ) SumAndMax_col__col__dollar_max_31 ) )) )
      (forall
       (
        (n0_61 (_ BitVec 3)))
       (not
        (=
         (arr_27 n0_61 ) SumAndMax_col__col__dollar_sum_35 ) )) )
     (forall
      (
       (n0_63 (_ BitVec 3)))
      (forall
       (
        (n0_62 (_ BitVec 3)))
       (or
        (and true
         (= n0_62 n0_63 ) )
        (not
         (=
          (arr_27 n0_62 )
          (arr_27 n0_63 ) ) ) ))) )

    (and
     (and true
      (not
       (= SumAndMax_col__col__dollar_max_31 SumAndMax_col__col__dollar_sum_35 ) ) ) true )

    (and true true )

          ; Assumptions for sorts bvsub there is at least one object of every sort:

    (exists
     (
      (x_0_64 (_ BitVec 5)))
     (type_of_SumAndMax_13_14 x_0_64 ))

    (exists
     (
      (x_0_65 (_ BitVec 5)))
     (type_of_Null_36_37 x_0_65 ))

    (exists
     (
      (x_0_66 (_ BitVec 5)))
     (type_of_any_23_24 x_0_66 ))

    (exists
     (
      (x_0_67 (_ BitVec 2)))
     (type_of_Heap_9_10 x_0_67 ))

    (exists
     (
      (x_0_68 (_ BitVec 5)))
     (type_of_java_dot_lang_dot_Object_3_4 x_0_68 ))

    (exists
     (
      (x_0_69 (_ BitVec 5)))
     (type_of_int_Array_0_1 x_0_69 ))

    (exists
     (
      (x_0_70 (_ BitVec 5)))
     (type_of_boolean_19_20 x_0_70 ))

    (exists
     (
      (x_0_71 (_ BitVec 4)))
     (type_of_Field_16_17 x_0_71 ))

)          ; End of assumptions.


          ; The formula to be proved:


   (=>
    (and
     (and
      (and
       (and
        (and
         (and
          (and
           (and
            (and
             (and
              (and
               (and
                (and
                 (and
                  (or
                   (bvsle
                    (length_7 a_2 ) k_0_8 )
                   (bvslt k_0_8 #b000 ) )
                  (wellFormed_12 heap_11 ) )
                 (=
                  (boolean_col__col_select_21 heap_11 self_15 java_dot_lang_dot_Object_col__col__abo_created_abc__18 ) TRUE_22 ) )
                (=
                 (SumAndMax_col__col_exactInstance_25 self_15 ) TRUE_22 ) )
               (=
                (boolean_col__col_select_21 heap_11 a_2 java_dot_lang_dot_Object_col__col__abo_created_abc__18 ) TRUE_22 ) )
              (bvsge
               (length_7 a_2 ) #b000 ) )
             (forall
              (
               (i_26 (_ BitVec 3)))
              (or
               (or
                (bvsle i_26
                 (bvsub #b000 #b001 ) )
                (bvsge i_26
                 (length_7 a_2 ) ) )
               (bvsge
                (int_col__col_select_28 heap_11 a_2
                 (arr_27 i_26 ) ) #b000 ) )) )
            (wellFormed_12 anon_heap_loop_29 ) )
           (bvsge k_0_8 #b000 ) )
          (bvsge
           (length_7 a_2 ) k_0_8 ) )
         (forall
          (
           (i_30 (_ BitVec 3)))
          (or
           (or
            (bvsle i_30
             (bvsub #b000 #b001 ) )
            (bvsge i_30 k_0_8 ) )
           (bvsle
            (int_col__col_select_28 heap_11 a_2
             (arr_27 i_30 ) )
            (int_col__col_select_28 anon_heap_loop_29 self_15 SumAndMax_col__col__dollar_max_31 ) ) )) )
        (=>
         (= k_0_8 #b000 )
         (=
          (int_col__col_select_28 anon_heap_loop_29 self_15 SumAndMax_col__col__dollar_max_31 ) #b000 ) ) )
       (=>
        (bvsge k_0_8 #b001 )
        (exists
         (
          (i_32 (_ BitVec 3)))
         (and
          (and
           (bvsge i_32 #b000 )
           (bvsle i_32
            (bvadd
             (bvsub #b000 #b001 ) k_0_8 ) ) )
          (=
           (int_col__col_select_28 heap_11 a_2
            (arr_27 i_32 ) )
           (int_col__col_select_28 anon_heap_loop_29 self_15 SumAndMax_col__col__dollar_max_31 ) ) )) ) )
      (=
       (bsum_34 #b000 k_0_8
        (int_col__col_select_28 heap_11 a_2
         (arr_27 i_33 ) ) )
       (int_col__col_select_28 anon_heap_loop_29 self_15 SumAndMax_col__col__dollar_sum_35 ) ) )
     (bvsge
      (bvmul
       (int_col__col_select_28 anon_heap_loop_29 self_15 SumAndMax_col__col__dollar_max_31 ) k_0_8 )
      (int_col__col_select_28 anon_heap_loop_29 self_15 SumAndMax_col__col__dollar_sum_35 ) ) )
    (or
     (= self_15 null )
     (= a_2 null ) ) )
)          ; End of imply.
))          ; End of assert.


(check-sat)
          ; end of smt problem declaration
