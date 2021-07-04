
public interface Seq<E extends Object> {

    /*@
      @ ensures !pastEnd() <==> ( pos().equals( \old(pos()) + 1) );
      @ ensures pastEnd() <==> ( \old(pos()).equals(length()) );
      @*/
    void forth();

    /*@
      @ requires !pastEnd();
      @ ensures 1 <= \result;
      @ ensures \result <= length();
      @*/
    /*@ non_null pure @*/ Integer pos();

    /*@
      @ requires !pastEnd();
      @*/
    /*@ non_null @*/ E current();

    /*@
      @ ensures 0 <= \result;
      @*/
    /*@ non_null pure @*/ Integer length();

    /*@ non_null pure @*/ Boolean pastEnd();
}
