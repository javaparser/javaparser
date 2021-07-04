
public class C {

    //+K2-K2@ requires x; // Type-check error when enabled
    void m() {}

    //-K1-K2@ requires x; // Type-check error when enabled
    void n() {}
    
    //+K1+K3@ requires x; // Type-check error when enabled
    void p() {}
}
