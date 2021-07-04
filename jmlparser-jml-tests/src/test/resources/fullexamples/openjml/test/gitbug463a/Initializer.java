public class Initializer {
    public int a;

    /*@ public normal_behavior
      @   ensures this.a == a;
      @ pure */
    public Initializer(int a) {
        this.a = a;
    }

    /*@ public normal_behavior
      @   requires a < 1000000; assignable a; // limit just to avoid overflow warnings
      @   ensures this.a == \old(this.a) + 1;
      @   ensures \fresh(\result);
      @   ensures \result.equals(new Initializer(\old(a)));
      @*/
    public Initializer dupe() {
        Initializer other = new Initializer(a);
        a++;
        return other;
    }

    /*@ also public normal_behavior
      @   assignable \nothing;
      @   ensures \result <==> obj instanceof Initializer && ((Initializer) obj).a == a;
      @*/
    public /*@ pure @*/ boolean equals(Object obj) {
        return obj instanceof Initializer && ((Initializer) obj).a == a;
    }
}