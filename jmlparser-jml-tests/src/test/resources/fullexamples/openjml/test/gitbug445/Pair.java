import java.util.ArrayList;
public class Pair<T> {
    protected /*@ spec_public @*/ T first, second;

    /*@ ensures first == fst && second == snd; 
      @ pure @*/
    public Pair(T fst, T snd) { first = fst; second = snd; }

    /*@ ensures \result == first; pure @*/
    public T getFirst() { return first;
    }
    /*@ ensures \result == second; pure @*/
    public T getSecond() { return second;
    }
    /*@ public model_program { 
      @   normal_behavior
      @     ensures res != null && res instanceof ArrayList<S> 
      @          && res.size() == 2;
      @   res.add(0,p.run(first));
      @   res.add(1,p.run(second));
      @   return res;
      @ } @*/
    public <S> ArrayList<S> mapToAl(Proc<T,S> p) {
        ArrayList<S> res = new ArrayList<S>(2);
        res.add(0, p.run(first));
        res.add(1, p.run(second));
        return res;
    }
}
