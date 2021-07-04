/**
 * Copyright (c) 1999 GEMPLUS group. All Rights Reserved.
 *------------------------------------------------------------------------------
 *  Project name:  PACAP  - cas d'�tude -
 *
 *
 *  Platform    :  Java virtual machine
 *  Language    :  JAVA 1.1.x
 *  Devl tool   :  Symantec VisualCafe
 *
 *  @version 1.0.
 *------------------------------------------------------------------------------
 */


package sv_rac;


/**
 * The class Decimal allows to represent virgule number. We use to
 * represent a number two short that correspond to the entire part and
 * the decimal part. Two important notes about a decimal number: it is
 * limited to 32767 (short representation) and the decimal part must
 * be done in the interval [000,999]. The operation are exact for the
 * addition and subtraction and rounded for the multiplication. The
 * division is not implemented because it is the terminal that it does
 * this action */
public class Decimal extends Object{
    ////////////////      ATTRIBUTES       ////////////////
    
    /**
     *	Nombre � virgule trop grand
     */
    public static final short DECIMAL_OVERFLOW   = (short)0x9F15;
    public static final short MAX_DECIMAL_NUMBER = (short)32767;
    
    /** save stack maximum length */
    /*@ spec_public */ private static final byte MAX_DEPTH = (byte) 1;
    

    /*@
      public invariant decPart >= 0 && decPart < PRECISION ;
      public invariant intPart >= 0 && intPart <= MAX_DECIMAL_NUMBER;
      public invariant intPart == MAX_DECIMAL_NUMBER ==> decPart == 0;
    */

    /** decimal precision */
    public static final short PRECISION      = (short) 1000;
    
    /** entere part */
    /*@ spec_public */ private short intPart = (short) 0;
    /** decimal part */
    /*@ spec_public */ private short decPart = (short) 0;

    /*@    
      public invariant decPart_ >= 0 && decPart_ < PRECISION ;
      public invariant intPart_ >= 0 ;
      public invariant intPart_ == MAX_DECIMAL_NUMBER ==> decPart_ == 0;
    */

    // save entere and decimal part
    /*@ spec_public */ private short intPart_ = intPart;
    /*@ spec_public */ private short decPart_ = decPart;
    
    /** save stack present length */
    // invariant 0 <= depth && depth <= MAX_DEPTH;
    /*@ spec_public */  private byte depth = (byte) 0;

    
    ///////////////     CONSTRUCTOR     ////////////////
   
    /*@ 
      requires true;
      ensures intPart == 0 && decPart == 0;
      ensures \fresh(this);
    */
    public Decimal() {
	super();
	intPart = (short) 0;
	decPart = (short) 0;
    }

    /*@ 
      requires v >= 0;
      ensures intPart == v && decPart == 0;
      ensures \fresh(this);
      exsures (ISOException) false;
    */ 
    // Code modified by Nestor CATANO 23/05/2001
    // inclusion of throws clause
    public Decimal(short v) 
	throws ISOException  {
        this();
        try{
            this.setValue(v);
        }
        catch(DecimalException e){
            //@ unreachable;
            throw new ISOException();			
        }
    }

    /*@ 
      requires i >= 0 && d >= 0 && d < PRECISION;
      requires i == MAX_DECIMAL_NUMBER ==> d == 0;
      ensures intPart == i && decPart == d;
      ensures \fresh(this);
      exsures (ISOException) false; assignable \everything;
    */   
    // Code modified by Nestor CATANO 23/05/2001
    // inclusion of throws clause
    public Decimal(short i, short d)
	throws ISOException {
        this();
        try{
            this.setValue(i,d);
        }
        catch(DecimalException e){
            //@ unreachable;
        	throw new ISOException();
        }
    }

    /*@ 
      requires d != null; 
      ensures intPart == d.intPart && decPart == d.decPart;
      ensures \fresh(this);
      exsures (ISOException) false;
    */  
    // Code modified by Nestor CATANO 23/05/2001
    // inclusion of throws clause  
    public Decimal(Decimal d)
	throws ISOException {
        this();
        try{
            setValue(d);
        }
        catch(DecimalException e){
            //@ unreachable;
        	throw new ISOException();
        }
    }
    
    ////////////////       METHODS      ///////////////
    
    
    //-------------------------------------------------------------------------
    //
    //                        aritmetic methods
    //
    //-------------------------------------------------------------------------

    /**
        @return the Decimal added by the value of the Decimal d
    */
    /*@
      modifies intPart, decPart; 
      requires d != null;
//       ensures intPart * PRECISION + decPart == 
//                 \old(intPart * PRECISION + decPart) + 
//                 d.intPart * PRECISION + d.decPart;
      ensures \result == this ;
      exsures (DecimalException) intPart < 0 ;
     */
        public Decimal add(Decimal d) throws DecimalException{
	    add(d.getIntPart(), d.getDecPart());            
 	    if(intPart < 0) 
       	throw new DecimalException();
	    return this;
	}               
    
    /**
        @return the Decimal substracted by the value of the Decimal d
    */
    /*@
      requires d != null;
      modifies intPart, decPart;
//       ensures intPart * PRECISION + decPart == 
//                 \old(intPart * PRECISION + decPart) - 
//                 d.intPart * PRECISION + d.decPart;
      ensures \result == this;
      exsures (DecimalException) intPart < 0;
    */
     public Decimal sub(Decimal d) throws DecimalException{
        add( (short) -d.getIntPart(), (short) -d.getDecPart());
        if(intPart < 0) 
        	throw new DecimalException();
        return this;
     }
    
    /**
        @return the Decimal multiplied by the value of the Decimal d
    */
    /*@
      modifies intPart, decPart;
      requires d != null ;
//       ensures intPart * PRECISION + decPart == 
//                 \old(intPart * PRECISION + decPart) * 
//                 (d.intPart * PRECISION + d.decPart);
      ensures \result == this ;
      exsures (DecimalException) intPart < 0 ;
    */
    public Decimal mul(Decimal d) throws DecimalException{
        mul(d.getIntPart(), d.getDecPart());
        if(intPart < 0)
        	throw new DecimalException();
        return this;
     }
    
    /**
        @return the oppose value of the Decimal d
    */
    /*@ 
      modifies intPart, decPart;
      requires true;     
      ensures intPart == \old((short)-intPart);
      ensures decPart == \old((short)-decPart);
      ensures \result == this;
      //exsures (RuntimeException) false
    */
    // Code modified by Marieke Huisman, 24/10/2001
    // Method changed from public to private
    // Cf. email Hugues Martin, Gemplus
    /*@ helper */ private Decimal oppose(){
        intPart = (short) -intPart;
        decPart = (short) -decPart;
        return this;
    } 


    /**
        @return the around to the nexte entere value
    */
    /*@ 
      modifies intPart, decPart;
      requires true;
      ensures \result == this;
      ensures decPart == 0;
      ensures intPart == (\old(decPart) >= (PRECISION/2) ?
                              (short)(\old(intPart) + 1) :
                                 (short)(\old(intPart)));
      //exsures (RuntimeException)false
    */
    public Decimal round(){        
	// MH, 29/10/01, commented out wrong code
//         short aux = decPart;
//         if ( aux < 0 ) aux = (short) -aux;
//         while ( aux > 10 ) aux /= (short) 10;
//         if ( aux > 5 ) {
// 	    if ( decPart > 0 ) intPart++;
// 	    else intPart = intPart --;
//         }
//         decPart = (short) 0;
//         return this;
	if (decPart >= (PRECISION/2) && intPart != MAX_DECIMAL_NUMBER) 
          intPart++;
        decPart = (short) 0;
        return this;
    }
        
    
    //-------------------------------------------------------------------------
    //
    //                          comparaison methods
    //
    //-------------------------------------------------------------------------
    
    
    /**
        comprae this decimal with the entere in parameter
        @param ref entere
        @return 0  if this == ref, 
                1  if this > ref,
               -1  if this < ref
    */
    /*@ 
      //modifies \nothing
      requires 0 <= ref && ref <= MAX_DECIMAL_NUMBER;
      ensures \result == (intPart == ref ? ((decPart == 0) ? 0 : 1)
                                         : ((intPart < ref) ? -1 : 1));
      //exsures (RuntimeException)false      
    */
    public short compareTo(short ref){
        short resu = (short) (intPart - ref );
        if ( resu == (short ) 0 ){          
            if ( decPart != 0 ) {
                resu = (short) ( decPart > (short) 0 ? (short) 1 : (short) -1 );           
	    }
        }
        else  resu = (short) ( resu > (short) 0 ? (short) 1 : (short) -1 );
        return resu;
    }
        
    
    /**
       Test if the Decimal is equal to 0
    */
    /*@
      //modifies \nothing
      requires true;
      ensures \result == (intPart == 0 && decPart == 0);
      //exsures (RuntimeException)false
    */
    public boolean isNull(){
        return ( compareTo((short) 0) == (short) 0);
    }
    
    
    /**
       Test if the Decimal is superior to 0
    */
    /*@ 
      //modifies \nothing
      requires true;
      ensures \result;
      //exsures (RuntimeException)false
    */
    public boolean isPositif(){
        return (compareTo((short) 0) >= (short) 0 );
    }
    
    
    /**
       Test if the Decimal is inferior to 0
    */
    /*@ 
      //modifies \nothing
      requires true;
      ensures \result == false;
      //exsures (RuntimeException)false
    */
    public boolean isNegatif(){
        return (compareTo((short) 0) < (short) 0 );
	//        return (compareTo((short) 0) <= (short) 0 );
    }
    

    
    /**
       Test if the Decimal is great or equal than the Decimal d 
    */
    /*@
      //modifies \nothing
      requires d != null;
      ensures \result == ((intPart * PRECISION + decPart >
                           d.intPart * PRECISION + d.decPart) ||
                          (intPart * PRECISION + decPart ==
                           d.intPart * PRECISION + d.decPart));
      //exsures (RuntimeException)false
    */
    public boolean isGreaterEqualThan(Decimal d){
        boolean resu = false;
        if      (intPart > d.getIntPart())   resu = true;
        else if (intPart < d.getIntPart())   resu = false;
        else if (intPart == d.getIntPart()){        
//             if      ((decPart > d.getDecPart())||(decPart > d.getDecPart()))   resu = true;
            if      ((decPart > d.getDecPart())||(decPart == d.getDecPart()))   resu = true;
            else if (decPart < d.getDecPart())   resu = false;
        }
        return resu;
    }
    
    /**
       Test if the Decimal is small or equal than the Decimal d
    */
    /*@ 
      //modifies \nothing
      requires d != null;
//       ensures \result == (intPart * PRECISION + decPart <= 
//                           d.intPart * PRECISION + d.decPart);
      //exsures (RuntimeException)false
    */
    public boolean isSmallerEqualThan(Decimal d){
        boolean resu = false;
        resu = ! isGreaterThan(d);
		return resu;
    }
    
    /**
        Test if the Decimal is great than the Decimal d
    */
    /*@ 
      //modifies \nothing
      requires d != null;
//       ensures \result == (intPart * PRECISION + decPart > 
//                           d.intPart * PRECISION + d.decPart);
      //exsures (RuntimeException)false
    */
    public boolean isGreaterThan(Decimal d) {
        return ( isGreaterEqualThan(d) && ! equal(d) );
    }
    
    /**
        Test if the Decimal is small than the Decimal d
    */
    /*@ 
      //modifies \nothing
      requires d != null;
//       ensures \result == (d.intPart * PRECISION + d.decPart >
//                           intPart * PRECISION + decPart);
      //exsures (RuntimeException)false
    */
    public boolean isSmallerThan(Decimal d){
        return ( isSmallerEqualThan(d) && ! equal(d));
    }
    
    /**
        Test if the Decimal is equal than the Decimal d
    */
    /*@ 
      //modifies \nothing
      requires d != null;
      ensures \result == (intPart == d.intPart &&
                          decPart == d.decPart);
      //exsures (RuntimeException)false
    */
    public boolean equal(Decimal d){
        return ( intPart == d.getIntPart() && decPart == d.getDecPart() );
        
    }
    
    //-------------------------------------------------------------------------
    //
    //                            accesor methods
    //
    //-------------------------------------------------------------------------
    
    
    /**
       Set the decimal value
    */

    /*@ 
      requires true;
      ensures intPart == v ;
      ensures decPart == (short) 0 ;
      ensures \result == this;
      exsures (DecimalException) v < 0;
    */
    public Decimal setValue(short v) throws DecimalException{
	// MH, 29/10/01, commented out wrong code
// 	intPart = v;
// 	if(intPart < 0)
// 	    decimal_exception.throwIt((byte)0x01 /*decimal_exception.DECIMAL_OVERFLOW*/);
// 	decPart = (short) 0;
// 	return this;
	if(v < 0)
    	throw new DecimalException();
	intPart = v;
	decPart = (short) 0;
	return this;
    }
    
    /**
        Set two short part to a decimal value
    */
    /*@ 
      requires true;
      ensures intPart == i && decPart == d ;
      ensures \result == this;
      exsures (DecimalException) i < 0 || d < 0 || d >= PRECISION || 
                                 (i == MAX_DECIMAL_NUMBER && d != 0);
    */ 
    public Decimal setValue(short i, short d) throws DecimalException{
	// NCC, 21/10/01, commented out wrong code
// 	intPart = i;
// 	decPart = d;
// 	if(intPart < 0)
// 	decimal_exception.throwIt((byte)0x01 /*decimal_exception.DECIMAL_OVERFLOW*/);
// 	return this;
	if(i < 0 || d < 0 || d >= PRECISION ||
           (i == MAX_DECIMAL_NUMBER && d != 0))
    	throw new DecimalException();
	
	intPart = i;
	decPart = d;
	return this;
    }
    
    
    /**
       Set a decimal value to a decimal value
    */
    /*@ 
      requires d != null ;
      ensures intPart == d.intPart ;
      ensures decPart == d.decPart ;
      ensures \result == this ;
      exsures (DecimalException) false ;
    */ 
    public Decimal setValue(Decimal d) throws DecimalException{
        return setValue(d.getIntPart(),d.getDecPart());
    }
    
    
    //code added by Nestor CATANO 12/10/01 to compile
    //Purse and PurseApplet classes
    public short setValue(byte buffer[], short d){
	return d ;
    }
    
    
    
    /**
       Acess to the entere part
    */
    /*@ 
      //modifies \nothing
      requires true;
      ensures \result == intPart;
      //exsures (RuntimeException)false
    */
    public short getIntPart(){
	return intPart;
    }
    
    /**
       Acess to the decimal part
    */
    /*@ 
      //modifies \nothing;
      requires true ;
      ensures \result == decPart;
      //exsures (RuntimeException)false
    */
        public short getDecPart(){
            return decPart;
        }
    
    /**
     *  return the entere value next the Decimal
    */
    /*@
      modifies intPart, decPart;
      requires true;
      ensures intPart == \old(intPart) && decPart == \old(decPart);
      ensures \result == (decPart >= PRECISION/2 ?
                          intPart + 1: 
                          intPart);
      //exsures (RuntimeException)false
    */
    public short getRoundedValue(){
        short resu = 0;
        short int_ = intPart;
        short dec_ = decPart;
        resu = round().getIntPart();
        intPart = int_;
        decPart = dec_;
        return resu;
    }
    
    /**
     * Put the Decimal value in the table bArray in two conscutive short 
     * @param bArray destinantion table
     * @param off loaction in the table
     * @return off + 4
    */
    /*@
      modifies bArray[off], bArray[off+1], bArray[off+2], bArray[off+3];
      requires bArray != null ;
      requires off >= 0;
      requires off + 3 < bArray.length;
      ensures \result == off+4 ;
      exsures (ArrayIndexOutOfBoundsException) false;
    */
    // Code modified by Nestor CATANO 21/05/2001
    // inclusion of throws clause
    public short getValue(byte [] bArray, short off) 
	throws TransactionException,
	       ArrayIndexOutOfBoundsException{
        short resu = off;
        resu  = setShort(bArray,resu,intPart);        
        resu  = setShort(bArray,resu,decPart);
        return resu;
    }
    
	//-----------------------------------------------------------------------
	//
	//          save method and value restoration
	//
	//-----------------------------------------------------------------------
	
	/** save the value of Decimal in the stack */
    /*@
      modifies intPart_, decPart_, depth;
      requires true;
      ensures (depth < MAX_DEPTH) ==> (intPart_ == intPart && 
                                       decPart_ == decPart &&
                                       depth == (byte) (\old(depth) + 1));
      //exsures (RuntimeException)false
    */
	public void saveValue(){
	    if ( depth < MAX_DEPTH ) {
	        intPart_ = intPart;
	        decPart_ = decPart;
		// MH, 29/10/01, code added
                depth++;
	    }
	}
	
	/** restore the value of the Decimal */
    /*@
      modifies intPart, decPart, depth;
      requires true;
      ensures (depth > 0) ==> (intPart == intPart_ && 
                               decPart == decPart_ && 
                               depth == (byte)(\old(depth) - 1));
      //exsures (RuntimeException)false
    */
    public void restoreValue(){
	if (depth > 0 ){
	    intPart = intPart_;
	    decPart = decPart_;
	    depth--;
	}
    }
	
	
    //-------------------------------------------------------------------------
    //
    //                            private methods
    //
    //-------------------------------------------------------------------------
    
    
    /**
     * add the entere part e and the decimal part f to a Decimal
     */
    /*@
      modifies intPart, decPart ;
      requires true ;
//       ensures intPart * PRECISION + decPart ==
//                \old(intPart * PRECISION + decPart) + (e * PRECISION + f);
      //exsures (RuntimeException)false;
    */
    private void add(short e, short f){
        intPart += e;
	
        if ( intPart > 0 && decPart < 0 ) {                        
            intPart--;
            decPart = (short) (decPart + PRECISION);            
        }
        else if ( intPart < 0 && decPart > 0 ){
            intPart++;
            decPart =(short) (decPart - PRECISION);
        }
        
        decPart += f;
        if ( intPart > 0 && decPart < 0 ) {                        
            intPart--;
            decPart = (short) (decPart + PRECISION);            
        }
        else if ( intPart < 0 && decPart > 0 ){
            intPart++;
            decPart = (short) (decPart - PRECISION);
        }
        else {
	    
            short retenue = (short) 0;
            short signe = 1;
            if ( decPart < 0 ) {
                signe = (short) -1;
                decPart = (short) -decPart;
            }        
            retenue = (short) (decPart / PRECISION);
            decPart = (short) (decPart % PRECISION);
            retenue *= signe;
            decPart *= signe;        
            intPart += retenue;        
        }   
    }//@ nowarn;
    
    /**
     * Multiplication of the Decimal by a entere part e and a decimal part f
     */
    /*@
      modifies intPart, decPart;
      requires true ;
//       ensures intPart * PRECISION + decPart == 
//               \old(intPart * PRECISION + decPart) * (e * PRECISION + f);
      // exsures (RuntimeException)false;
    */
    private void mul(short e, short f){
	
        short intBackup = intPart; 
        short decBackup = decPart;
        
	//a * b = a * (int(b) + frac(b)) = a * int(b) + a* frac(b)
        
        short nbIter = e;        
        if ( nbIter < 0 ) { nbIter = (short) -nbIter;}
        intPart = (short) 0;
        decPart = (short) 0;
        for ( short i = (short) 0; i < nbIter; i++){
            add(intBackup, decBackup);
        }
        if ( e < 0 ) { oppose(); }
        
        short intPart_ = intPart;
        short decPart_ = decPart;
        intPart = (short) 0;
        decPart = (short) 0;
        nbIter = intBackup;
        if ( nbIter < 0 ) { nbIter = (short) -nbIter; }
        for ( short i = (short) 0; i < nbIter; i++ ){
            add((short) 0, f);
        }
        if (intBackup < 0 ) { oppose(); }
        
        add(intPart_, decPart_);
        
        short signe = (short)1;
        
        short arrondis1 = decBackup;                
        if ( arrondis1 < 0 ) {
           arrondis1 = (short)  -arrondis1;
           signe = (short) -signe;
        }
        short arrondis2 = f;
        if ( arrondis2 < 0 ) {
            arrondis2 = (short) -arrondis2;
            signe = (short) -signe;
        }
        
        short decal = (short) 0;
        while ( arrondis1 > 100 ) {
            arrondis1 /= (short) 10;
            decal++;
        }
        while ( arrondis2 > 100 ) {
            arrondis2 /= (short) 10;        
            decal++;
        }
        short temp = (short)  (arrondis1 * arrondis2);        
        
        short aux = (short) 1000;
        while ( decal > 0 ) {
            aux /= (short) 10;
            decal--;
        }
        //@ assume aux != 0;
        temp /= aux;
        temp *= signe;
        
        
        add((short) 0, temp);        
    }//@ nowarn;
    
    static short setShort(byte[] array, short offset, short value) {
    	array[offset++] = (byte)((value >> 8) & 0xFF);
    	array[offset++] = (byte)(value & 0xFF);
    	return offset;
    }
    
    public static void main(String[] args) throws ISOException, DecimalException {
    	Decimal d = new Decimal((short)10, (short)5);
    	d.add(d);
    	d.sub(d);
    	
    	
    }
}

