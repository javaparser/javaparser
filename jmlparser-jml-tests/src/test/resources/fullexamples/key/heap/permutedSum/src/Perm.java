/**
 * Compute a sum of integers through the order given by an iterator.
 * The exact order is not known, except for the fact that each element
 * is selected exactly once.
 * For simplicity, this implementation uses an array instead of a
 * (generic) collection type.
 * @author Daniel Bruns
 */
class Perm {

  int[] a;

  /*@ normal_behavior
    @ requires pIdx == 0;
    @ ensures \result == (\sum int j; 0 <= j && j < a.length; a[j]);
    @*/
  int foo() {
      int s = 0;
      /*@ maintaining s == (\sum int i; 0 <= i && i < pIdx; (int)c[i]);
        @ maintaining \invariant_for(this);
        @ decreasing a.length - pIdx;
        @ assignable pIdx;
        @*/
      while (hasNext())
          s+= next();
      return s;
  }

  /*@ ghost \seq perm; // permutation on indices
    @ ghost int pIdx;
    @ invariant 0 <= pIdx && pIdx <= a.length;
    @ invariant perm.length == a.length;
    @ invariant \dl_seqNPerm(perm);
    @
    @ ghost \seq b; // a as seq
    @ invariant b == (\seq_def int i; 0; a.length; a[i]);
    @
    @ ghost \seq c; // a permuted by perm
    @ invariant \dl_seqPerm(b,c);
    @ invariant (\forall int i; 0 <= i && i < c.length;
    @               (int)c[i] == (int)b[(int)perm[i]]);
    @ invariant (\forall int i; 0 <= i && i < c.length;
    @               c[i] == (int)c[i]);
    @ invariant c.length == a.length;
    @*/

  /*@ normal_behavior
    @ ensures \result == (pIdx < a.length);
    @ strictly_pure helper
    @*/
  native boolean hasNext();

  /*@ normal_behavior
    @ requires pIdx < a.length;
    @ ensures \result == (int)c[\old(pIdx)];
    @ ensures pIdx == \old(pIdx)+1;
    @ assignable pIdx;
    @*/
  native int next();

}
