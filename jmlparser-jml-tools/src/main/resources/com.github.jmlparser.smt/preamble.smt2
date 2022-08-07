(declare-sort Object 0)
(declare-const null Object)

(declare-fun instanceOf (Object Object) Bool)

(declare-fun Integer2int (Object) (Array $a $b))
(declare-fun Integer2BV32 (Object) (_ BitVec 32))

(declare-fun to_array (Object) (Array $a $b))
