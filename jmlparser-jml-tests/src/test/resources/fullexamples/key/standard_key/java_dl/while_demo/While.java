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

class While {

    static void loop2(int i) {
	int j; 
	while (i>0) {
	    if (i==3) {
		return;
	    } 
	    
	}
    }


    static int loop22(int i) {
	tt: while (i>0) {
	    if (i==3) {
		break;
	    } 
	    switch (i) {
	    case 1: i++; break ;
	    }
	    i++;
	    
	}
	int helper=0;
	return i;
    }

    static void loop3(int i) {

	l:{while (i>0) {
		if (i==3) {
		    continue;
		} 
		int k;
		l5:while (true) {
		    if (i==6) 
			continue;
		    if (i==7)
			continue l5;
		}
		
	    }
	}
    }

    static void loop4(int i) {

	l:{while (i>0) {
		if (i==3) {
		    break;
		} 
		int k;
		l5:while (true) {
		    if (i==6) 
			break;
		    if (i==7)
			break l;
		}
		
	    }
	}
    }


    static int loop(int b){
	return loop((byte)b);
    }
    
    static byte loop(byte i){
	try {
	    int j; 
	    while (i>0) {
		if (i==3) {
		    i--; 
		    continue;
		} 
		if (i==4) {
		    i--; 
		    return (byte)i;
		} 
		i--;
	    }
	} catch (Exception e){}
	return i;
    }

}
