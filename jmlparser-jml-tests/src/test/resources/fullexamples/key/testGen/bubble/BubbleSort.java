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

public class BubbleSort{

    public int[] b;

    /*@ public normal_behavior
      @  requires a!=null && a.length>1 && a.length<5;
      @  requires a.length == b.length && 
      @           (\forall int i; 0<=i && i<a.length; b[i]==a[i]);
      @  ensures a!=null ==> (\forall int i; 0<=i && i<a.length-1; 
      @                        a[i]<=a[i+1]) &&
      @                      equalsModOrdering(a, b); 
      @*/
    public void sort(int[] a){
	if(a==null) return;
	boolean sorted = false;
	int help;
	while(!sorted){
	    sorted=true;
	    for(int i=0; i<a.length-1; i++){
		if(a[i]>a[i+1]){
		    help = a[i];
		    a[i] = a[i+1];
		    a[i+1] = help;
		    sorted = false;
		}
	    }
	}	
    }

    public static /*@pure@*/ boolean equalsModOrdering(int[] a, int[] b){
	if(a.length!=b.length){
	    return false;
	}
	int[] x = new int[a.length];
	int[] y = new int[a.length];
	copy(a, x);
	copy(b, y);
	return equalsModOrderingHelp(x, y, 0);
    }

    private static void copy(int[] a, int[] b){
	for(int i=0; i<a.length; i++){
	    b[i] = a[i];
	}
    }

    private static boolean equalsModOrderingHelp(int[] a, int[] b, int start){
	if(start>=a.length) return true;
	int i = find(a[start], b, start);
	if(i==-1){
	    return false;
	}
	b[i] = b[start];
	return equalsModOrderingHelp(a, b, start+1);
    }

    private static int find(int x, int[] ar, int i){
	while(i < ar.length){
	    if(ar[i] == x){
		return i;
	    }
	    i++;
	}
	return -1;
    }

}
