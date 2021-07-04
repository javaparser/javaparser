import java.util.Scanner;

public class GCDCalculatorMain{
    //@ requires System.out.isOpen && System.err.isOpen;
    //@ requires \invariant_for(System.out);
    //@ requires \invariant_for(System.err);
	public static void main(String[] args){
		try{ 
			int num1, num2, gcd;
			GCDCalculator a = new GCDCalculator();
			Scanner input = new Scanner(System.in);
			
			System.out.println("Enter the first Number.");
			num1 = input.nextInt();

			System.out.println("Enter the first Number.");
			num2 = input.nextInt();

			if(num1 == (Integer.MAX_VALUE) || num2 == (Integer.MAX_VALUE)){
				System.err.println("Number can not be Max Integer Values.");
				return;
			}
 
						 		
			if((num1 == 0 && num2 ==0) || num1 <= (Integer.MIN_VALUE + 1) || num2 <= (Integer.MIN_VALUE + 1)) {
				System.err.println("Both numbers cannot be zero. Or any of the be the Minimum Integer number.");
				return;
			}


			gcd = a.GCD(num1, num2);

			System.out.println("GCD of "+ num1 + " and " + num2 + " is equal to " + gcd);
		}
		catch (Exception e){
		    //@ assume \invariant_for(System.err);
		    //@ assume System.err.isOpen;
			System.err.println("Scanner Exception!");
                        e.printStackTrace(System.err);
			return;
		}

	}
}
