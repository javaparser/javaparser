/** This demonstrates JML specifications with initially clauses.
 *  Proofs in KeY run completely automatically (if overflows are ignored).
 *  @author Daniel Bruns
 */
public class Initially {

  protected /*@spec_public@*/ int x;
  //@ public initially x > 0;

  public Initially (int y) {
    x = (y>0?y:-y+1);
  }

  public Initially (boolean b) {
    x = b ? 1: 42;
  }

  public Initially (Object[] a) {
    x = a.length+1;
  }
}
