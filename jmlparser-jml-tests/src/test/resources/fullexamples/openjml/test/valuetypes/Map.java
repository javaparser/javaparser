//@ pure
public class Map<K,V> {
    
    //@ ensures map.<K,V>empty().get(k) == null;
    //@ model public static <K,V> void newMapIsEmpty(K k) {}
    
    //@ ensures s.put(k,v).get(k) == v;
    //@ model public static <K,V> void putGet(map<K,V> s, K k, V v) {}
    
    //@ ensures k != kk ==> s.put(k,v).get(kk) == s.get(kk);
    //@ model public static <K,V> void putGet2(map<K,V> s, K k, V v, K kk) {}
    
}