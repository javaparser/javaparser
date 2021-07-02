package mini;

/**
 *
 * @author christoph
 */
public class MiniExamplesLecture {
    public static int l;
    private static int h;

    /*@ normal_behavior
      @     determines l \by \itself;
      @*/
    void m_1() {
        l = h;
    }

    /*@ normal_behavior
      @     determines l \by \itself;
      @*/
    void m_2() {
        if (l>0) {h=1;} else {h=2;};
    }

    /*@ normal_behavior
      @     determines l \by \itself;
      @*/
    void m_3() {
        if (h>0) {l=1;} else {l=2;};
    }

    /*@ normal_behavior
      @     determines l \by \itself;
      @*/
    void m_4() {
        h=0; l=h;
    }

    /*@ normal_behavior
      @     determines l \by \itself;
      @*/
    void m_5() {
        l=h; l=l-h;
    }

    /*@ normal_behavior
      @     determines l \by \itself;
      @*/
    void m_6() {
        if (false) l=h;
    }

}
