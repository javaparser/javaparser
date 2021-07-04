// Originally, this submitted example crashed in RAC but passed ESC.
// The problem was divide by zero in the body of quantifiers, which was
// nont being c hecked by ESC. Also, the main routine now proves much quicker
// when using an uninterpreted function in place of explicit mod.

public class GCDCalculator{

	//@ public normal_behavior     
        //@ requires d != 0;
        //@ pure function
        public static int div(int n, int d) { return n%d; }
     //@ requires num1 != Integer.MAX_VALUE && num1 != Integer.MAX_VALUE && num1 > Integer.MIN_VALUE + 1 && num2 > Integer.MIN_VALUE + 1;
     //@ {|  
	//@ requires num1 != 0 && num2 != 0;
	//@ old int tnum1 = Math.abs(num1);
	//@ old int tnum2 = Math.abs(num2);
	//@ old int greater = (tnum1 > tnum2) ? tnum1 : tnum2;
	//@ old int smaller = (tnum1 > tnum2) ? tnum2 : tnum1;
	//@ ensures \result > 0;
	//@ ensures div(tnum1,\result) == 0;
	//@ ensures div(tnum2,\result) == 0;
	//@ ensures (\forall int i; i > \result && i <= smaller; div(smaller,i) == 0 ==> div(greater,i) != 0);

	//@ also

	//@ requires num1 == 0 && num2 != 0;
	//@ requires num2 != Integer.MIN_VALUE;
	// @ old int tnum2a = Math.abs(num2);
	//@ ensures \result == Math.abs(num2);

	//@ also

	//@ requires num1 != 0 && num2 == 0;
	//@ requires num1 != Integer.MIN_VALUE;
	//@ old int tnum1a = Math.abs(num1);  // FIXME: If we eliminnate this old clause, things work, but otherwise not.
	//@ ensures \result == \lbl TNUM1a tnum1a;
      //@ |}

	public int GCD(int num1, int num2)throws IllegalArgumentException {

		int gcd = 1; 
		

		if(num1 == Integer.MIN_VALUE || num2 == Integer.MIN_VALUE)
		{
			 throw new IllegalArgumentException("Input values cannot be the minimum integer values."); 
		}

		AbsoluteValue a = new AbsoluteValue();

	 	num1 = a.IntAbsolute(num1);
		
		num2 = a.IntAbsolute(num2);
	
		//@ assume div(num1, gcd) == 0 && div(num2, gcd) == 0;

		if(num1 == 0 && num2 == 0){	
			throw new IllegalArgumentException("GCD(0, 0) is not defined.");
		}

		if(num1 == 0 || num2 == 0){ 
		    //@ show \old(num1), \old(num2), num1, num2, num1>num2, Integer.MAX_VALUE;
			return (num1 > num2) ? num1 : num2;
		}

		//@ maintaining gcd <= num1 && gcd <= num2;
		//@ maintaining i > 0 && i <= num1 + 1 && i<= num2 + 1; 
		//@ maintaining 0 < gcd && gcd <= i;
		//@ maintaining div(num1, gcd) == 0 && div(num2, gcd) == 0;
		//@ maintaining (\forall int j; 1 <= j &&  j<i; div(num1, j) == 0 && div(num2, j) == 0 ==> j <= gcd);
		//@ decreases num1 - i; 
		for(int i = 1; i <= num1 && i <= num2; i++){
            		if(div(num1,i) == 0 && div(num2,i) == 0){
               			gcd = i;
			}
        	}
		return gcd;
	} 

}
