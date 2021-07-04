import org.jmlspecs.annotation.*;

/** Documentation of class A */
public class AEnum {


// NESTED CLASSES

/** DOcumentation for class B. */
@Pure
static public class B { }

/** Documentation for a model nested class but not BNInterface. */
//@ static @Model public class MB {  }

// ENUMS
/** */
public static enum consts { EA, EB, EC }

/** Model enum */
//@ model protected static enum mconsts { MEA, MEB }

// ANNOTATIONS

/** */
public static @interface Annot {}

/** Model annotation */
//@ model public @interface MAnnot {}



}


