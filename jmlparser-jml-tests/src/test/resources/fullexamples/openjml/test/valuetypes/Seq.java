//import org.jmlspecs.lang.seq;

//@ pure
public class Seq<T> {
    
    //@ ensures seq.<T>empty().isEmpty();
    //@ ensures seq.<T>empty().size() == 0;
    //@ model public static <T> void newSeqIsEmpty() {}
    
    //@ ensures s.add(k).size() == 1 + s.size();
    //@ model public static <T> void addBumpsSize(seq<T> s, T k) {}
    
    //@ requires 0 <= i && i <= s.size();
    //@ ensures s.add(i,k).size() == 1 + s.size();
    //@ model public static <T> void addBumpsSize(seq<T> s, T k, \bigint i) {}
    
    //@ requires 0 <= k && k < s.size();
    //@ ensures (\lbl RS s.remove(k).size()) == s.size() - 1;
    //@ model public static <T> void removeLowersSize(seq<T> s, int k) { show s.size(), k; }
    
    //@ public normal_behavior
    //@   requires i >= 0 && i <= s.size();
    //@   ensures seq.equals(s.add(i,t).remove(i), s);
    //@ model public static <T> void addRemove(seq<T> s, T t, \bigint i) {}
    
    
    
}
//
//class SeqTest {
//    
//    
//    //@ requires s.size() > 100;
//    /*@ model public void m(seq<\bigint> s) {
//        //@ ghost \bigint b1 = s.get(0);
//        //@ ghost \bigint b2 = s.get(0);
//        //@ assert b1 == b2;
//    }*/
//    
//    //@ requires s.size() > 100;
//    /*@ model public void mm(seq<long> s) {
//        //@ ghost long b1 = s.get(0);
//        //@ ghost long b2 = s.get(0);
//        //@ assert b1 == b2;
//    }*/
//    
//
//}