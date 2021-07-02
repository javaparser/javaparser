package mini;

/**
 * Information flow examples.
 *
 * A collection of mini examples related to aliasing.
 *
 * @author christoph
 */
public class AliasingExamples {
    int x;
    
    /*@ requires a != b;
      @ determines \result, b.x \by \itself;
      @*/
    int secure_1(AliasingExamples a, AliasingExamples b, int h) {
        a.x = h;
        return b.x;
    }
    
    /*@ determines \result, b.x \by \itself;
      @*/
    int insecure_1(AliasingExamples a, AliasingExamples b, int h) {
        a.x = h;
        return b.x;
    }
}
