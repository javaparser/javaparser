package tp;

public class PVis {

public int ip_public;
protected int ip_protected;
int ip_package;
private int ip_private;

//@ ghost public int gp_public;
//@ ghost protected int gp_protected;
//@ ghost int gp_package;
//@ ghost private int gp_private;

public void mp_public() {};
protected void mp_protected() {}
void mp_package() {}
private void mp_private() {}

//@ model public void qp_public() {};
//@ model protected void qp_protected() {}
//@ model void qp_package() {}
//@ model private void qp_private() {}

/** public constructor */
public PVis() {}
/** protected constructor */
protected PVis(int i) {}
/** package constructor */
PVis(int i, int j) {}
/** private constructor */
private PVis(int i, int j, int k) {}

/** public model constructor */
//@ model public PVis(Object o) {}
/** protected model constructor */
//@ model protected PVis(float i) {}
/** package model constructor */
//@ model PVis(float i, float j) {}
/** private model constructor */
//@ model private PVis(float i, float j, float k) {}


public static class Cp_public {}
protected static class Cp_protected {}
static class Cp_package {}
private static class Cp_private {}

//@ model public static class Dp_public {}
//@ model protected static class Dp_protected {}
//@ model static class Dp_package {}
//@ model private static class Dp_private {}

public static enum EP_public { EPA }
protected static enum EP_protected { EPB }
static enum EP_package { EPC }
private static enum EP_private { EPD }

/** public nested model enum */
//@ model public static enum EMp_public { EMAp }
/** protected nested model enum */
//@ model protected static enum EMp_protected { EMBp }
/** package nested model enum */
//@ model static enum EMp_package { EMCp }
/** private nested model enum */
//@ model private static enum EMp_private { EMDp }

/** public nested interface */
public static interface Ip_public {  }
/** protected nested interface */
protected static interface Ip_protected {  }
/** package nested interface */
static interface Ip_package {  }
/** private nested interface */
private static interface Ip_private {  }

/** public nested model interface */
//@ model public static interface IMp_public {  }
/** protected nested model interface */
//@ model protected static interface IMp_protected {  }
/** package nested model interface */
//@ model static interface IMp_package {  }
/** private nested model interface */
//@ model private static interface IMp_private {  }

/** public nested annotation */
public static @interface Ap_public {  }
/** protected nested annotation */
protected static @interface Ap_protected {  }
/** package nested annotation */
static @interface Ap_package {  }
/** private nested annotation */
private static @interface Ap_private {  }

/** public nested model annotation */
//@ model public static @interface AMp_public {  }
/** protected nested model annotation */
//@ model protected static @interface AMp_protected {  }
/** package nested model annotation */
//@ model static @interface AMp_package {  }
/** private nested model annotation */
//@ model private static @interface AMp_private {  }


}

