public class LinkedList {
    private /*@ nullable @*/ LinkedList next ;
    //@ model int index ;
    //@ represents index \such_that next == null || index < next.index ;

    //@ requires index == index;
    //@ ensures this != next;
    public void foo(){}
}

