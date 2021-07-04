//@ model import org.jmlspecs.lang.set;

//@ pure
public class Locset {
    
    //@ public normal_behavior
    //@ ensures locset.locset().empty();
    //@ model public static void newLocSetIsEmpty() {}
    
    //@ public normal_behavior
    //@ ensures locset.locset().add(o).size() == 1;
    //@ model public static void singleton(location o) {}
    
    //@ public normal_behavior
    //@ ensures !s.contains(o) ==> s.add(o).size() == 1 + s.size();
    //@ model public static void addBumpsSize(locset s, location o) {}
    
    //@ public normal_behavior
    //@ ensures s.contains(o) ==> s == s.add(o);
    //@ ensures s.contains(o) ==> s.add(o).size() == s.size();
    //@ model public static void addDoesNotChangeSize(locset s, location o) {}
    
    //@ public normal_behavior
    //@ ensures !s.contains(o) ==> locset.equals(s.add(o).remove(o), s);
    //@ model public static void addRemove(locset s, location o) {}
    
    //@ public normal_behavior
    //@ ensures s.contains(o) ==> locset.equals(s.add(o), s);
    //@ model public static void addNoChange(locset s, location o) {}
    
    //@ public normal_behavior
    //@ ensures !s.contains(o) ==> locset.equals(s, s.remove(o));
    //@ model public static void addRemoveA(locset s, location o) {}
    
    //@ public normal_behavior
    //@ ensures s.contains(o) ==> s.remove(o).size() == s.size() - 1;
    //@ model public static void addRemoveB(locset s, location o) {}
    
    void m() {
        //@ ghost locset s = locset.locset();
        //@ ghost locset ss = s;
        //@ ghost \locset sss = s;
        //@ assert s == ss;
        //@ assert ss == sss;
    }
    
}