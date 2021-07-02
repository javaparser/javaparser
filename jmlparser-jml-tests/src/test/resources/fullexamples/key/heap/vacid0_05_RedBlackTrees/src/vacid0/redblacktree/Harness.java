// Copyright (C) 2011 Daniel Bruns
// Published under Modified BSD License
// See LICENSE for details.


package vacid0.redblacktree;

/**
 * Harness suggested by Leino and Moskal.
 * Not implementation-aware (makes only use of the map interface).
 * @author bruns
 *
 */
public class Harness {

    //@ requires a.isEmpty && a.defaultValue == 0 && \invariant_for(a);
    //@ requires b.isEmpty && b.defaultValue == 1 && \invariant_for(b);
    //@ requires \disjoint(a.footprint,b.footprint);
  public static void redBlackTestHarness(AbstractMap a, AbstractMap b) {
    a.replace(1, 1); 
    b.replace(1, 10);
    a.replace(2, 2); 
    b.replace(2, 20);
    assert(a.lookup(1) == 1 && a.lookup(42) == 0);
    assert(b.lookup(1) == 10 && b.lookup(42) == 1);
    a.remove(1); 
    b.remove(2);
    assert(a.lookup(1) == 0 && a.lookup(42) == 0);
    assert(b.lookup(2) == 1 && b.lookup(42) == 1);
  }
  
  
  // *** Some simpler tests *** //
  
  //@ requires a.isEmpty && \invariant_for(a) && a.defaultValue == 0 && 0 <= k && k < a.contents.length;
  public static void testEmpty(AbstractMap a, int k) {
    assert a.lookup(k) == 0;
  }

  //@ requires a.isEmpty && \invariant_for(a) && a.defaultValue == 0;
  public static void testSimpleReplaceAndRemove(AbstractMap a) {
    a.replace(1, 1); 
    assert(a.lookup(1) == 1);
    assert(a.lookup(42) == 0);
    a.remove(1);
    assert(a.lookup(1) == 0);

  }
  
  //@ requires \invariant_for(a) && \invariant_for(b);
  //@ requires \disjoint(a.footprint,b.footprint);
  //@ ensures \disjoint(a.footprint,b.footprint);
  public static void testDisjointnessPreservation(AbstractMap a, AbstractMap b){
      a.replace(3, 27);
  }
  
  
  public static void main(String[] arrrgggh){
      redBlackTestHarness(new RedBlackTree(0), new RedBlackTree(1));
  //    System.out.println("Test harness successfully passed.");
  }

}
