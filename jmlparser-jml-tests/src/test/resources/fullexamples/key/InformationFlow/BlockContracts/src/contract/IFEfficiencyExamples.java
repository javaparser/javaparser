package contract;


/**
 *
 * @author christoph
 */
public class IFEfficiencyExamples {
    private int h;
    public int l;

    //@ determines l \by \itself;
    void mWithBlockContract() {
        // fix l value
        //@ normal_behavior determines l \by \itself;
        { if (l < 0) { l = 0;} }
        //@ normal_behavior determines l \by \itself;
        { if (l > 8) { l = 8; } }

        // fix h value
        //@ normal_behavior determines l \by \itself;
        { if (h < 0) { h = 0; } }
        //@ normal_behavior determines l \by \itself;
        { if (h > 8) { h = 8; } }

        // calculate h result
        //@ normal_behavior determines l \by \itself;
        { h = h * l; }
    }

    //@ determines l \by \itself;
    void mWithoutBlockContract() {
        // fix l value
        if (l < 0) { l = 0; }
        if (l > 8) { l = 8; }

        // fix h value
        if (h < 0) { h = 0; }
        if (h > 8) { h = 8; }

        // calculate h result
        h = h * l;
    }

}
