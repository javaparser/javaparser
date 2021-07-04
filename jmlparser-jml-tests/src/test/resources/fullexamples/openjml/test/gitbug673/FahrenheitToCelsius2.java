import java.util.Scanner;
//@ model import org.jmlspecs.models.JMLFloat;

    
class FahrenheitToCelsius2 {
	/*@ spec_public */static double Celsius;
     
	//@ requires Double.isFinite(temperature);
    //@ assignable Celsius, System.out.outputText;
    // FIXME: @ ensures Double.isFinite(\result);
    // FIXME: @ ensures JMLFloat.approximatelyEqualTo(\result, (((temperature - 32)*5)/9), 0.1) == true;
    //@ ensures Math.abs(\result - (((temperature - 32)*5)/9)) <= 0.1;
	public static double Temperature2(double temperature) {
	
       
     
        Celsius = ((temperature - 32)*5)/9;
     
        System.out.println("temperature in Celsius = " + Celsius);
        return Celsius;
    }
     public static void main(String[] args) {
	     double temperature;
         Scanner in = new Scanner(System.in);
     
         System.out.println("Enter temperature in Fahrenheit");
         temperature = in.nextFloat();
         //@ assume Double.isFinite(temperature);
	     Temperature2(temperature);
       }
    }
