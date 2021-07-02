package object;


/**
 *
 * @author christoph
 */
public class AmtoftBanerjee {

    int q;

    //@ normal_behavior
    //@ assignable \nothing;
    //@ determines \result \by q;
    int getQ() {
        return this.q;
    }

    // final to make method expansion modularly sound
    final void setQ(int n) {
        this.q = n;
    }


    static int secret, z;

    //@ normal_behavior
    //@ determines z \by secret;
    //@ also
    // the following contract is not satisfied
    //@ normal_behavior
    //@ determines z \by \nothing;
    static void m_1() {
        AmtoftBanerjee x1;
        AmtoftBanerjee x2 = new AmtoftBanerjee();
        x1 = x2;
        x1.setQ(secret);
        z = x2.getQ();
    }

    //@ normal_behavior
    //@ determines z \by \nothing;
    static void m_2() {
        AmtoftBanerjee x1 = new AmtoftBanerjee();
        AmtoftBanerjee x2 = new AmtoftBanerjee();
        x1.setQ(secret);
        z = x2.getQ();
    }
}
