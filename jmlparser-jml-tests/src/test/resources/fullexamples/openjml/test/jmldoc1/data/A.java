import org.jmlspecs.annotation.*;

/** Documentation of class A */
@Pure
public class A extends BB implements BInterface {

// CONSTRUCTORS

/** Documentation of a constructor with specs */
//@ requires true;
public A() {}

/** Documentation of a constructor without specs */
public A(@org.jmlspecs.annotation.Nullable Object o, /*@ nullable*/ Object oo) {}

/** Documentation for a model constructor with specs. */
//@ requires i == 0;
//@ model public A(int i) {}

//@ requires i == 0.0;
//@ model public A(float i) {}

//@ requires i == null;
//@ model public A(Object i) {}

/** Documentation for a model constructor with no specs. */
//@ model public A(int i,int j, @NonNull Object k , non_null Object m) {}

//@ requires j >= 0;
//@ model public A(float nodocs ,int j , int k) {}

// CLASS SPECS

//@ invariant true;
//@ constraint false;
//@ initially true;
//@ axiom true;

//@ represents bb_model = 0;

// ENUMS
/** */
public static enum consts { EA, EB, EC }

/** Model enum */
// FIXME  @ model protected static enum mconsts { MEA, MEB }

// ANNOTATIONS

/** */
public static @interface Annot {}

/** Model annotation */
//@ model public @interface MAnnot {}


// FIELDS

/** Documentation for a model field */
/*@
 public secret model int i;
 secret represents i = 0;
*/

/** Documentatino for a ghost field and for fboth */
/*@
 ghost int ghost_i;
*/

public A a;

/*@ non_null */ @Secret
public Object fboth;
//@ in i;
//@ maps a.i \into i;

/*@ non_null */ @Secret
public Object fannot_nodocs; //@ in i;

protected Object fnone_nodocs;

public @Secret Object fclauses_nodocs;
//@ in i;
//@ maps a.i \into i;


// METHODS

/** Documentation for a model method with specs - adl */
//@ also requires true;
//@ model @Deprecated Object adl(int i);

/** Documentation for a model method mdl_nospecs and for nodocnospecs */
//@ model int mdl_nospecs(int i);

//@ requires i == 0;
//@ model void ambig(int i);

//@ requires i == 0.0;
//@ model void ambig(float i);

//@ requires i == null;
//@ model void ambig(Object i);

//@ requires i == "";
//@ model void ambig(String i);


@Deprecated
public void nodocnospecs() {}

/** Doc but no specs */
public void docnospecs() {}

/** Documentation of method m with specs. More info. */
//@ requires true;
//@ ensures \result == 0;
//@ signals (java.io.FileNotFoundException e) true;
//@ signals_only java.io.FileNotFoundException;
@Pure
public int m(@NonNull Object o) { return 0; }

/** Documentation of method m with specs. More info. */
//@ requires true;
//@ ensures \result == 0;
//@ modifies a;
//@ signals (java.io.FileNotFoundException e) true;
//@ signals_only java.io.FileNotFoundException;
public int mmod(@NonNull Object o) { return 57; }

//@ requires true;
//@ ensures \result == 0;
//@ signals (java.io.FileNotFoundException e) true;
//@ signals_only java.io.FileNotFoundException;
@Pure
public int mm(Object o) { return 42; }


@NonNull
public Object n(String s) { return new Object(); }

/** @param s input
    @return output
*/
/*@ non_null */
public Object nn(/*@ non_null */ String s) { return new Object(); }

//@ public normal_behavior
//@  requires true;
//@  ensures true;
//@ also public behavior
//@  requires false;
//@  ensures false;
@Query
public void q() {}

public void tttt(@NonNull Object a, /*@ nullable */ Object b, /*@ non_null */ Object c, @Nullable Object d) {}

// NESTED CLASSES

/** DOcumentation for class B. */
@Pure
static public class B {

//@invariant false && true;
}

/** Documentation for a model nested class but not BNInterface. */
//@ static @Model public class MB { invariant true;  void qqq() {} }
//@ static model public class MC extends BB {}

/**/
@Pure
public static interface BNInterface_nodoc { /*@ invariant false; */ }

/** Documentation for a model nested interface. */
//@ model public static interface BMInterface {}

}

interface BInterface extends BEInterface { 
/*@ invariant false; */ 

//@ ensures false;
//@ model Object adl(int i);

//@ ensures false;
int mm(Object o);

}

interface BEInterface {

/*@ invariant false && false; */ 

//@ ensures false && false;
//@ model @NonNull Object adl(int i);

//@ ensures false && false;
int mm(Object o);

}

class BB {

public int z_public;

//@ invariant false;

//@ ensures z_public == 10;
public int mm(Object o) { return 0; }

//@ ensures z_public == 11;
public int mm() { return 0; }

//@ public model int mdla();
//@ public model int mdlb();
//@ private model void mdlc();

//@ ghost public int bb_ghost;
//@ model public int bb_model;
//@ ghost private int bb_private;

static public class BBB {}
//@ model static public class BBBM {}
}

class CEmpty {
//@ model public CEmpty(Object o) {}
//@ ghost public int ghhost_i;
//@ model public int model_i;
//@ model public int model_m();
//@ model public static class CNested {}
}

//@ model class CCM {}

