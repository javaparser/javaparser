public class Declarations {
    //@ public model int abc;

    /*@
      ensures abc == 9;
      forall int local;
      requires local != 0;
     */
    public void foo() {
        //@assert abc == 0;
    }
}
