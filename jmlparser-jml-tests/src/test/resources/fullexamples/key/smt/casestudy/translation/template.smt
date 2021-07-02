; BIT_HEAP #BIT_HEAP 
; BIT_OBJECT #BIT_OBJECT
; BIT_INT #BIT_INT
; BIT_FIELD #BIT_FIELD
(set-option :print-success true) 

(set-option :produce-unsat-cores true)

(set-option :produce-models true)

(set-option :produce-proofs true)

          ; Declaration of sorts.

(declare-sort u 0)
          ; Predicates used in formula:


(declare-fun wellFormed_12 
 (#BIT_HEAP ) Bool )
          ; Types expressed by predicates:


(declare-fun type_of_SumAndMax_13_14 
 (#BIT_OBJECT ) Bool )

(declare-fun type_of_Null_36_37 
 (#BIT_OBJECT ) Bool )

(declare-fun type_of_any_23_24 
 (#BIT_OBJECT ) Bool )

(declare-fun type_of_Heap_9_10 
 (#BIT_HEAP ) Bool )

(declare-fun type_of_int_5_6 
 (#BIT_INT ) Bool )

(declare-fun type_of_java_dot_lang_dot_Object_3_4 
 (#BIT_OBJECT ) Bool )

(declare-fun type_of_int_Array_0_1 
 (#BIT_OBJECT ) Bool )

(declare-fun type_of_boolean_19_20 
 (#BIT_OBJECT ) Bool )

(declare-fun type_of_Field_16_17 
 (#BIT_FIELD ) Bool )

          ; Function declarations

(declare-fun heap_11 
 () #BIT_HEAP )

(declare-fun dummy_Field_46 
 () #BIT_FIELD )

(declare-fun dummy_java_dot_lang_dot_Object_43 
 () #BIT_OBJECT )

(declare-fun dummy_boolean_45 
 () #BIT_OBJECT )

(declare-fun k_0_8 
 () #BIT_INT )

(declare-fun i_33 
 () #BIT_INT )

(declare-fun length_7 
 (#BIT_OBJECT ) #BIT_INT )

(declare-fun self_15 
 () #BIT_OBJECT )

(declare-fun dummy_Heap_41 
 () #BIT_HEAP )

(declare-fun boolean_col__col_select_21 
 (#BIT_HEAP #BIT_OBJECT #BIT_FIELD  ) #BIT_OBJECT )

(declare-fun a_2 
 () #BIT_OBJECT )

(declare-fun dummy_any_40 
 () #BIT_OBJECT )

(declare-fun bsum_34 
 (#BIT_INT #BIT_INT #BIT_INT ) #BIT_INT )

(declare-fun anon_heap_loop_29 
 () #BIT_HEAP )

(declare-fun dummy_int_Array_44 
 () #BIT_OBJECT )

(declare-fun null 
 () #BIT_OBJECT )

(declare-fun java_dot_lang_dot_Object_col__col__abo_created_abc__18 
 () #BIT_FIELD )

(declare-fun dummy_SumAndMax_38 
 () #BIT_OBJECT )

(declare-fun SumAndMax_col__col__dollar_max_31 
 () #BIT_FIELD )

(declare-fun arr_27 
 (#BIT_INT ) #BIT_FIELD )

(declare-fun SumAndMax_col__col_exactInstance_25 
 (#BIT_OBJECT ) #BIT_OBJECT )

(declare-fun dummy_Null_39 
 () #BIT_OBJECT )

(declare-fun SumAndMax_col__col__dollar_sum_35 
 () #BIT_FIELD )

(declare-fun int_col__col_select_28 
 (#BIT_HEAP #BIT_OBJECT #BIT_FIELD ) #BIT_INT )

(declare-fun TRUE_22 
 () #BIT_OBJECT )

(declare-fun dummy_int_42 
 () #BIT_INT )

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
      (tvar_47 #BIT_HEAP)) 
     (forall 
      (
       (tvar_48 #BIT_OBJECT)) 
      (forall 
       (
        (tvar_49 #BIT_FIELD)) 
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
      (tvar_50 #BIT_INT)) 
     (type_of_Field_16_17 
      (arr_27 tvar_50 ) ))

    (forall 
     (
      (tvar_51 #BIT_OBJECT)) 
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
      (tvar2_52 #BIT_OBJECT)) 
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
      (tvar2_55 #BIT_OBJECT)) 
     (=> 
      (type_of_java_dot_lang_dot_Object_3_4 tvar2_55 ) 
      (type_of_any_23_24 tvar2_55 ) ))

    (forall 
     (
      (tvar2_56 #BIT_OBJECT)) 
     (=> 
      (type_of_int_Array_0_1 tvar2_56 ) 
      (type_of_java_dot_lang_dot_Object_3_4 tvar2_56 ) ))

    (forall 
     (
      (tvar2_57 #BIT_OBJECT)) 
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
          (n0_59 #BIT_INT)) 
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
         (n0_60 #BIT_INT)) 
        (not 
         (= 
          (arr_27 n0_60 ) SumAndMax_col__col__dollar_max_31 ) )) ) 
      (forall 
       (
        (n0_61 #BIT_INT)) 
       (not 
        (= 
         (arr_27 n0_61 ) SumAndMax_col__col__dollar_sum_35 ) )) ) 
     (forall 
      (
       (n0_63 #BIT_INT)) 
      (forall 
       (
        (n0_62 #BIT_INT)) 
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

          ; Assumptions for sorts - there is at least one object of every sort:

    (exists
     (
      (x_0_64 #BIT_OBJECT))
     (type_of_SumAndMax_13_14 x_0_64 ))

    (exists
     (
      (x_0_65 #BIT_OBJECT))
     (type_of_Null_36_37 x_0_65 ))

    (exists
     (
      (x_0_66 #BIT_OBJECT))
     (type_of_any_23_24 x_0_66 ))

    (exists
     (
      (x_0_67 #BIT_HEAP))
     (type_of_Heap_9_10 x_0_67 ))

    (exists
     (
      (x_0_68 #BIT_OBJECT))
     (type_of_java_dot_lang_dot_Object_3_4 x_0_68 ))

    (exists
     (
      (x_0_69 #BIT_OBJECT))
     (type_of_int_Array_0_1 x_0_69 ))

    (exists
     (
      (x_0_70 #BIT_OBJECT))
     (type_of_boolean_19_20 x_0_70 ))

    (exists
     (
      (x_0_71 #BIT_FIELD))
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
                   (<= 
                    (length_7 a_2 ) k_0_8 ) 
                   (< k_0_8 0 ) ) 
                  (wellFormed_12 heap_11 ) ) 
                 (= 
                  (boolean_col__col_select_21 heap_11 self_15 java_dot_lang_dot_Object_col__col__abo_created_abc__18 ) TRUE_22 ) ) 
                (= 
                 (SumAndMax_col__col_exactInstance_25 self_15 ) TRUE_22 ) ) 
               (= 
                (boolean_col__col_select_21 heap_11 a_2 java_dot_lang_dot_Object_col__col__abo_created_abc__18 ) TRUE_22 ) ) 
              (>= 
               (length_7 a_2 ) 0 ) ) 
             (forall 
              (
               (i_26 #BIT_INT)) 
              (or 
               (or 
                (<= i_26 
                 (- 0 1 ) ) 
                (>= i_26 
                 (length_7 a_2 ) ) ) 
               (>= 
                (int_col__col_select_28 heap_11 a_2 
                 (arr_27 i_26 ) ) 0 ) )) ) 
            (wellFormed_12 anon_heap_loop_29 ) ) 
           (>= k_0_8 0 ) ) 
          (>= 
           (length_7 a_2 ) k_0_8 ) ) 
         (forall 
          (
           (i_30 #BIT_INT)) 
          (or 
           (or 
            (<= i_30 
             (- 0 1 ) ) 
            (>= i_30 k_0_8 ) ) 
           (<= 
            (int_col__col_select_28 heap_11 a_2 
             (arr_27 i_30 ) ) 
            (int_col__col_select_28 anon_heap_loop_29 self_15 SumAndMax_col__col__dollar_max_31 ) ) )) ) 
        (=> 
         (= k_0_8 0 ) 
         (= 
          (int_col__col_select_28 anon_heap_loop_29 self_15 SumAndMax_col__col__dollar_max_31 ) 0 ) ) ) 
       (=> 
        (>= k_0_8 1 ) 
        (exists
         (
          (i_32 #BIT_INT))
         (and 
          (and 
           (>= i_32 0 ) 
           (<= i_32 
            (+ 
             (- 0 1 ) k_0_8 ) ) ) 
          (= 
           (int_col__col_select_28 heap_11 a_2 
            (arr_27 i_32 ) ) 
           (int_col__col_select_28 anon_heap_loop_29 self_15 SumAndMax_col__col__dollar_max_31 ) ) )) ) ) 
      (= 
       (bsum_34 0 k_0_8 
        (int_col__col_select_28 heap_11 a_2 
         (arr_27 i_33 ) ) ) 
       (int_col__col_select_28 anon_heap_loop_29 self_15 SumAndMax_col__col__dollar_sum_35 ) ) ) 
     (>= 
      (* 
       (int_col__col_select_28 anon_heap_loop_29 self_15 SumAndMax_col__col__dollar_max_31 ) k_0_8 ) 
      (int_col__col_select_28 anon_heap_loop_29 self_15 SumAndMax_col__col__dollar_sum_35 ) ) ) 
    (or 
     (= self_15 null ) 
     (= a_2 null ) ) )
)          ; End of imply.
))          ; End of assert.


(check-sat)
          ; end of smt problem declaration
