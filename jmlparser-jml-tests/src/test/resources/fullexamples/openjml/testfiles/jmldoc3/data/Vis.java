public class Vis extends SVis {

/** public field */
public int i_public;
/** protected field */
protected int i_protected;
/** package field */
int i_package;
/** private field */
private int i_private;

/** public ghost field */
//@ ghost public int g_public;
/** protected ghost field */
//@ ghost protected int g_protected;
/** package ghost field */
//@ ghost int g_package;
/** private ghost field */
//@ ghost private int g_private;

/** public method */
public void m_public() {};
/** protected method */
protected void m_protected() {}
/** package method */
void m_package() {}
/** private method */
private void m_private() {}

/** public model method */
//@ model public void q_public() {};
/** protected model method */
//@ model protected void q_protected() {}
/** package model method */
//@ model void q_package() {}
/** private model method */
//@ model private void q_private() {}

/** public constructor */
public Vis() {}
/** protected constructor */
protected Vis(int i) {}
/** package constructor */
Vis(int i, int j) {}
/** private constructor */
private Vis(int i, int j, int k) {}

/** public model constructor */
//@ model public Vis(Object o) {}
/** protected model constructor */
//@ model protected Vis(float i) {}
/** package model constructor */
//@ model Vis(float i, float j) {}
/** private model constructor */
//@ model private Vis(float i, float j, float k) {}

/** public nested class */
public static class C_public {}
/** protected nested class */
protected static class C_protected {}
/** package nested class */
static class C_package {}
/** private nested class */
private static class C_private {}

/** public nested model class */
//@ model public static class D_public {}
/** protected nested model class */
//@ model protected static class D_protected {}
/** package nested model class */
//@ model static class D_package {}
/** private nested model class */
//@ model private static class D_private {}

/** public nested enum */
public static enum E_public { EA }
/** protected nested enum */
protected static enum E_protected { EB }
/** package nested enum */
static enum E_package { EC }
/** private nested enum */
private static enum E_private { ED }

/** public nested model enum */
//@ model public static enum EM_public { EMA }
/** protected nested model enum */
//@ model protected static enum EM_protected { EMB }
/** package nested model enum */
//@ model static enum EM_package { EMC }
/** private nested model enum */
//@ model private static enum EM_private { EMD }

/** public nested interface */
public static interface I_public {  }
/** protected nested interface */
protected static interface I_protected {  }
/** package nested interface */
static interface I_package {  }
/** private nested interface */
private static interface I_private {  }

/** public nested model interface */
//@ model public static interface IM_public {  }
/** protected nested model interface */
//@ model protected static interface IM_protected {  }
/** package nested model interface */
//@ model static interface IM_package {  }
/** private nested model interface */
//@ model private static interface IM_private {  }

/** public nested annotation */
public static @interface A_public {  }
/** protected nested annotation */
protected static @interface A_protected {  }
/** package nested annotation */
static @interface A_package {  }
/** private nested annotation */
private static @interface A_private {  }

/** public nested model annotation */
//@ model public static @interface AM_public {  }
/** protected nested model annotation */
//@ model protected static @interface AM_protected {  }
/** package nested model annotation */
//@ model static @interface AM_package {  }
/** private nested model annotation */
//@ model private static @interface AM_private {  }


}

class SVis extends tp.PVis {

public int is_public;
protected int is_protected;
int is_package;
private int is_private;

//@ ghost public int gs_public;
//@ ghost protected int gs_protected;
//@ ghost int gs_package;
//@ ghost private int gs_private;

public void ms_public() {}
protected void ms_protected() {}
void ms_package() {}
private void ms_private() {}

//@ model public void qs_public() {};
//@ model protected void qs_protected() {}
//@ model void qs_package() {}
//@ model private void qs_private() {}

/** public constructor */
public SVis() {}
/** protected constructor */
protected SVis(int i) {}
/** package constructor */
SVis(int i, int j) {}
/** private constructor */
private SVis(int i, int j, int k) {}

/** public model constructor */
//@ model public SVis(Object o) {}
/** protected model constructor */
//@ model protected SVis(float i) {}
/** package model constructor */
//@ model SVis(float i, float j) {}
/** private model constructor */
//@ model private SVis(float i, float j, float k) {}


public static class Cs_public {}
protected static class Cs_protected {}
static class Cs_package {}
private static class Cs_private {}

//@ model public static class Ds_public {}
//@ model protected static class Ds_protected {}
//@ model static class Ds_package {}
//@ model private static class Ds_private {}

public static enum ES_public { ESA }
protected static enum ES_protected { ESB }
static enum ES_package { ESC }
private static enum ES_private { ESD }

/** public nested model enum */
//@ model public static enum EMs_public { EMAs }
/** protected nested model enum */
//@ model protected static enum EMs_protected { EMBs }
/** package nested model enum */
//@ model static enum EMs_package { EMCs }
/** private nested model enum */
//@ model private static enum EMs_private { EMDs }

/** public nested interface */
public static interface Is_public {  }
/** protected nested interface */
protected static interface Is_protected {  }
/** package nested interface */
static interface Is_package {  }
/** private nested interface */
private static interface Is_private {  }

/** public nested model interface */
//@ model public static interface IMs_public {  }
/** protected nested model interface */
//@ model protected static interface IMs_protected {  }
/** package nested model interface */
//@ model static interface IMs_package {  }
/** private nested model interface */
//@ model private static interface IMs_private {  }

/** public nested annotation */
public static @interface As_public {  }
/** protected nested annotation */
protected static @interface As_protected {  }
/** package nested annotation */
static @interface As_package {  }
/** private nested annotation */
private static @interface As_private {  }

/** public nested model annotation */
//@ model public static @interface AMs_public {  }
/** protected nested model annotation */
//@ model protected static @interface AMs_protected {  }
/** package nested model annotation */
//@ model static @interface AMs_package {  }
/** private nested model annotation */
//@ model private static @interface AMs_private {  }


}
