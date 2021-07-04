
     
    public class FactorialFunction
    {
	//@ requires n >= 0 && n <= 20;
       public long FactoF(int n)
       {
          int c;
          long fact = 1;
	  
	   if ( n == 0) {
	      //@ assert fact == spec_factorial(n);          
              return fact;
	   }
	   //@ assert spec_factorial(0) == 1;

          //@ maintaining c >= 1 && c <= n+1;
	  //@ maintaining fact > 0;
	  //@ maintaining fact <= Long.MAX_VALUE; 
	  //@ maintaining spec_factorial(c - 1) == fact;
	  //@ decreases n - c;
          for (c = 1; c <= n; c++){
		//@ assert c <= n;
                //@ assume fact*c <= Long.MAX_VALUE;
                fact = fact*c;
             }	
	  //@ assert c == n+1;
	  //@ assert spec_factorial(c - 1) == fact;   
          return fact;
     }

	/*@ requires n > 0 && n <= 20;
            ensures 0 <= \result && \result <= Long.MAX_VALUE;
            ensures \result == n * spec_factorial(n-1);
           also
            requires n == 0;
            ensures \result == 1;
        public static model function pure long spec_factorial(int n){ 
	    if(n == 0) {
		 return 1; 
	    }
	    else {
		//@ assert n > 0 && n <= 20;
		//@ assume n * spec_factorial(n-1) <= Long.MAX_VALUE;
		return n * spec_factorial(n-1);
	    }

        }@*/
}
