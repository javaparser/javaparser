public class Test {
    
    //@ requires \nonnullelements(list.values);
    public void m1(java.util.List<Integer> list) {
        
        //@ loop_invariant \forall \bigint k; 0 <= k < \count; list.values[k] >= 0;
        for (Integer i: list) {
            // @ assert 0 <= \count < list.values.length;
            // @ assert i == list.values[\count];
            if (i < 0) return;
        }
        //@ assert \forall \bigint k; 0 <= k < list.values.length; list.values[k] >= 0;
    }
    
    //@ requires \nonnullelements(list);
    public void m2(Integer[] list) {
        
        //@ loop_invariant \forall \bigint k; 0 <= k < \count; list[k] >= 0;
        for (Integer i: list) {
            // @ assert 0 <= \count < list.length;
            // @ assert i == list[\count];
            if (i < 0) return;
        }
        //@ assert \forall \bigint k; 0 <= k < list.length; list[k] >= 0;
    }
}