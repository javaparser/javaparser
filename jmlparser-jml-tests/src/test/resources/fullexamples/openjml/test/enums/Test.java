enum EEC {
    
    AAA, BBB;
    EEC() {}
    
}

enum EEE {
    
    AA, BB, CC, DD;
}

public class Test {
    
    public void m0() {
        //@ assert EEE.AA == EEE.AA;
        //@ assert EEE.AA != EEE.BB;
    }
    
    //@ pure
    public void m2b() {
        //@ assert EEE.AA.toString() == EEE.AA.name();
    }
        
    //@ pure
    public void m2d() {
        //@ assert EEE.AA.name() == EEE.AA.name(); 
        //@ assert EEE.AA.name() != EEE.BB.name(); 
    }
    
    public void m3(EEE e) {
        //@ assert e == EEE.AA || e == EEE.BB || e == EEE.CC || e == EEE.DD;
    }
    
    public void m4(EEE e) {
        switch(e) {
        case AA: case BB: case CC:
           break;
        case DD:
            break;
        default:
            //@ unreachable; 
           break; 
        }
    }
    
    //@ pure
    public void m5(EEE e) {
        EEE[] ev = EEE.values();
        //@ assert ev.length == 4 ;
        //@ assert EEE.values() == EEE.values();
        //@ assert EEE.values() == e.values();
    }
    
    //@ pure
    public void m5b(EEE e) {
        //@ show EEE._JMLvalues, EEE._JMLvalues[0];
        EEE[] ev = EEE.values();
        //@ assert ev.length == 4 ;
        //@ assert ev[0] == EEE.AA;
        //@ assert ev[1] == EEE.BB;
        //@ assert ev[2] == EEE.CC;
        //@ assert ev[3] == EEE.DD;
    }
    
    //@ pure
    public void m5c(EEE e) {
        EEE[] ev = EEE.values();
        //@ assume (\forall EEE ee; ee != null ==> (\exists int i; 0<=i && i<ev.length; ev[i] == ee)); // FIXME - failig
        //@ assert ev.length == 4 ;
        boolean b = EEE.values() == e.values();
        //@ assert b;
    }
        
    //@ pure
    public void m5a(EEE e) {
        EEE[] ev = EEE.values();
        //@ assert (\exists int i; 0<=i && i<ev.length; ev[i] == e);  // FIXME - Failinng
    }
    
    //@ pure
    public void m6(/*@ nullable */ String s) {
        try {
            EEE e = Enum.valueOf(EEE.class,s); // might throw exception
            //@ assert e != null && s != null;
            //@ assert e == EEE.AA || e == EEE.BB || e == EEE.CC || e == EEE.DD;
        } catch (NullPointerException ex) {
            //@ assert s == null;
        } catch (IllegalArgumentException ex) {
            // FIXME - s is not any one of the possibilities
        }
    }
    
    //@ pure
    public void m6a(/*@ nullable */ String ssss) {
        try { EEE e = EEE.valueOf(ssss); // might throw exception
            //@ assert e != null;
            //@ assert ssss != null;
            //@ assert e == EEE.AA || e == EEE.BB || e == EEE.CC || e == EEE.DD;
        } catch (NullPointerException ex) {
            //@ assert ssss == null;
        } catch (IllegalArgumentException ex) {
            // FIXME - s is not any one of the possibilities
        }
    }
    
    //@ pure
    public void m7(EEE ee) {
        // @ assert EEE.AA.ordinal() == 0;
        // @ assert EEE.BB.ordinal() == 1;
        // @ assert EEE.CC.ordinal() == 2;
        // @ assert EEE.DD.ordinal() == 3;
        // @ assert ee.ordinal() >= 0;
        //@ assert ee.ordinal() < EEE.values().length;
    }
    
    //@ ensures !\fresh(\result);
    //@ pure
    public EEE m8(int i) {
        return EEE.AA;
    }
    
    //@ pure
    public void m9() {
        EEE e = m8(0);
        //@ assert \fresh(e); // false
    }
    
    //@ pure
    public void m9a() {
        EEE e = m8(0);
        //@ assert !\fresh(e);
    }
    
    
    
}