public class FactorialMain {
    public static void main(String args[]){
	int n = 14;
        long fact;
	Factorial tm = new Factorial();
         
          if (n < 0){
             System.out.println("Number should be non-negative.");
             return;
             }
          else if (n > 20){
             System.out.println("Number should be no more than 20.");
             return;
             }

	  else	
	     fact = tm.Facto(n);
          	
//         System.out.println("Factorial of "+n+" is = " + fact);	// Separate problem - cf. bigintToString
    }
}
