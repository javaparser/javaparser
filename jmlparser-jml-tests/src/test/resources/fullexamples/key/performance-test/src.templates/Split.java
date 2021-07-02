/**
 *
 * @author christoph
 */
public class Split {
    boolean x1, x2, x3, x4, x5, x6, x7, x8,
            x9, x10, x11, x12, x13, x14, x15, x16,
            x17, x18, x19, x20, x21, x22, x23, x24,
            x25, x26, x27, x28, x29, x30, x31, x32,
            x33, x34, x35, x36, x37, x38, x39, x40;


    /*@ requires    x1 == (x2 ? (x3 ? (x4 ? true : false) : false) : false);
        requires    x5 == (x6 ? (x7 ? (x8 ? true : false) : false) : false);
        requires    x9 == (x10 ? (x11 ? (x12 ? true : false) : false) : false);
        requires    x13 == (x14 ? (x15 ? (x16 ? true : false) : false) : false);
        requires    x17 == (x18 ? (x19 ? (x20 ? true : false) : false) : false);
        requires    x21 == (x22 ? (x23 ? (x24 ? true : false) : false) : false);
        requires    x25 == (x26 ? (x27 ? (x28 ? true : false) : false) : false);
        requires    x29 == (x30 ? (x31 ? (x32 ? true : false) : false) : false);
        requires    x33 == (x34 ? (x35 ? (x36 ? true : false) : false) : false);
        ensures     x1 == (x4 ? (x3 ? (x2 ? true : false) : false) : false);
     */
    void split(){
    }

}
