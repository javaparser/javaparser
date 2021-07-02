// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 




public class Decimal {

    private short intPart;
    private short decPart;
    
    
    public final static short PRECISION = 1000;

    public static final short DECIMAL_OVERFLOW	 = (short)0x9f15;	
	 
    public static final short MAX_DECIMAL_NUMBER = (short)0x7fff;


    /**
     * Implementation done by Gemplus
     */
    public void add(short e, short f) {


// New implementation by Breunesse and Jacobs
/*    intPart += e;
    decPart += f;
    if ( decPart >= PRECISION ) {
	decPart -= PRECISION;
	intPart++;
	}*/


	intPart += e;

	if ( intPart > 0 && decPart < 0 ) {
	    intPart--;
	    decPart = (short)( decPart + PRECISION );
	}
	else if ( intPart < 0 && decPart > 0 ) {
	    intPart++;
	    decPart = (short)( decPart - PRECISION );
	}

	decPart += f;
	if ( intPart > 0 && decPart < 0 ) {
	    intPart--;
	    decPart = (short)( decPart + PRECISION );
	}
	else if ( intPart < 0 && decPart > 0 ) {
	    intPart++;
	    decPart = (short)( decPart - PRECISION );
	}
	else {
	    short retenue = 0;
	    short signe = 1;
	    if ( decPart < 0 ) {
		signe = -1;
		decPart = (short)( -decPart );
	    }
	    retenue = (short)( decPart / PRECISION );
	    decPart = (short)( decPart % PRECISION );
	    retenue *= signe;
	    decPart *= signe;
	    intPart += retenue;
        }
    }

    
    /**
     * Implementation by Cees-Bart Breunesse
     */
    public void mul1(short e, short f) {

	       
        short intBackup = intPart; 
        short decBackup = decPart;
        
        // a * b = a * (int(b) + frac(b)) = a * int(b) + a* frac(b)
        
        intPart = (short) 0;
        decPart = (short) 0;

	short i = (short)0;
	while (i < e) {
	    add(intBackup, decBackup);
	    i++;
	}

//        for ( short i = (short) 0; i < e; i++){
//            add(intBackup, decBackup);
//        }

        short intPart_ = intPart;
        short decPart_ = decPart;
        intPart = (short) 0;
        decPart = (short) 0;

	short j = (short)0;
	while (j < intBackup) {
	    add((short)0, f);
	    j++;
	}

//        for ( short i = (short) 0; i < intBackup; i++ ){
//            add((short) 0, f);
//        }

        add(intPart_, decPart_);

        short arrondis1 = decBackup;                
        short arrondis2 = f;
        short decal = (short) 0;
        if ( arrondis1 > 100 ) {
            arrondis1 /= (short) 10;
            decal++;
        }
        if ( arrondis2 > 100 ) {
            arrondis2 /= (short) 10;        
            decal++;
        }

        short temp = (short)  (arrondis1 * arrondis2);        
        short aux = (short) (decal == 0 ? 1000 :
			     (decal == 1 ? 100 : 10));
        temp /= aux;
        add((short) 0, temp);



	/*	short a = intPart;
	short b = decPart;
	
	intPart = (short)0;
	decPart = (short)0;

	short i = (short)0;
	while (i < e) {
	    add(a, b);
	    i++;
	}
	
	short j = (short)0;
	while (j < a) {
	    add((short)0, f);
	    j++;
	}

	short b1 = (short)(b / 100);
	short b2 = (short)((b - b1 * 100) / 10);
	short b3 = (short)(b - b1 * 100 - b2 * 10);

	short l = (short)((b1 * f) / 10);
	short m = (short)((b2 * f) / 100);
	short n = (short)((b3 * f) / 1000);
	short gross = (short)(l + m + n);

	short q = (short)((b1 * f - l * 10) * 100);
	short r = (short)((b2 * f - m * 100) * 10);
	short s = (short) (b3 * f - n * 1000);
	short rest = (short)(q + r + s);

	add((short)0, (short)(gross + (rest / 1000))); */
    }


    /**
     * Implementation by Cees-Bart Breunesse
     */
    public void mul2(short e, short f) {

	short intBackup = intPart; 
        short decBackup = decPart;
        
        // a * b = a * (int(b) + frac(b)) = a * int(b) + a* frac(b)
        
        intPart = (short) 0;
        decPart = (short) 0;

	short i = (short)0;
	while (i < e) {
	    add(intBackup, decBackup);
	    i++;
	}

	short j = (short)0;
	while (j < intBackup) {
	    add((short)0, f);
	    j++;
	}

//        for ( short i = (short) 0; i < e; i++){
//            add(intBackup, decBackup);
//        }
//
//        for ( short i = (short) 0; i < intBackup; i++ ){
//            add((short) 0, f);
//        }

        short a1 = (short)(decBackup / 100);
        short a2 = (short)((decBackup - a1 * 100) / 10);
	short a3 = (short)(decBackup - a1 * 100 - a2 * 10);

	short d1a = (short)((a1 * f)/10);
	short d2a = (short)((a2 * f)/100);
	short d3a = (short)((a3 * f)/1000);
	short gross = (short)(d1a + d2a + d3a);

	short d1b = (short)((a1 * f - d1a * 10) * 100);
	short d2b = (short)((a2 * f - d2a * 100) * 10);
	short d3b = (short) (a3 * f - d3a * 1000);
	short rest = (short)(d1b + d2b + d3b);

        add((short) 0, (short)(gross+rest/1000));

    }
}
