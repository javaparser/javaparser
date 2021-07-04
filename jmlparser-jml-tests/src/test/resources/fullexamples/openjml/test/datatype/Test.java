public class Test {
    
    
    /*@
    static public datatype N {}
     */
    
    public void m() {
        
        //@ datatype X {};
    }
    
    /*@
    model
    public void mm(NN<Integer> x) {
        NN<Integer> xx = NN.<Integer>Empty();
        xx = NN.<Integer>Cons(1,xx);
        boolean b = xx.isEmpty();
        b = x.isCons();
        Integer i = xx.head();
        xx = xx.tail();
    }
    */
}

/*@
datatype NN<T> {
    Empty(),
    Cons(T head, NN<T> tail)
    ;
    
    int length() {
       return \match (this) {
         case Empty() -> 0;
         case Cons(_,t) -> 1+ t.length();
       };
     }

    NN<T> of(T t) { return Cons(t, Empty()); }
    
}
 */
