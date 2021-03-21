public class E {
    //@ invariant true;


    /*@ public normal_behavior
        forall int i;
        ensures true;
        requires x != x;
        assignable x,y,z;

        also

        private exceptional_behavior
        forall int x;
        signals_only Exception;
        signals (Exception e) true;
        {|
            ensures_free true;
            requires_free false;
        |}
     */
    public void t() {
        //@ assert true;
        //@ assume false;
        //@ hence_by false;
        //@ unreachable;
        //@ set a = 5;

        //+key@ assert true;
        //-key@ assert false;
        //-key+openjml@ assert false;
        //-key-openjml@ assert false;
        //-@ assert false;
        //+@ assert false;
    }
}
