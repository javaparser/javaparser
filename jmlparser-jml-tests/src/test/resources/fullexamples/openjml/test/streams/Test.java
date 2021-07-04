import java.util.Arrays;
import java.util.List;
import java.util.stream.*;

public class Test {
    
    
    public void m1(Integer[] a) {
        //@ reachable;
        Stream<Integer> s = Arrays.stream(a);
        //@ assert Arrays.equalElements(s.values,a);
        //@ reachable;
        Collector<Integer,?,List<Integer>> coll = Collectors.<Integer>toList();
        //@ assert coll == Collectors.<Integer>toList();
        //@ reachable;
        List<Integer> r = s.collect(coll);
        //@ reachable;
        //@ assert r.values == s.values;
        //@ assert Arrays.equalElements(r.values,s.values);
        // @ assert Arrays.equalElements(r.values,a);
    }
}