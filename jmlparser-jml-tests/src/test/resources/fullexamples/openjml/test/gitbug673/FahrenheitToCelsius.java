import java.util.Scanner;
//@ model import org.jmlspecs.models.JMLFloat;

    
class FahrenheitToCelsius {
	/*@ spec_public */static double Celsius;
     
    //@ requires Float.isFinite(temperature);
    //@ assignable Celsius, System.out.outputText;
    //@ ensures Double.isFinite(Celsius) && Float.isFinite(\result);
    // FIXME: @ ensures JMLFloat.approximatelyEqualTo(\result, (((temperature - 32)*5)/9), 0.1f) == true;
	public static float Temperature(float temperature) {
	
       
     
        Celsius = ((temperature - 32)*5)/9;
        //@ assume Double.isFinite(Celsius);
     
        System.out.println("temperature in Celsius = " + Celsius);
        //@ assume Float.isFinite((float)Celsius);
	    return (float)Celsius;
    }
     public static void main(String[] args) {
	     float temperature;
         Scanner in = new Scanner(System.in);
     
         System.out.println("Enter temperature in Fahrenheit");
         temperature = in.nextFloat();
         //@ assume Float.isFinite(temperature);
	     Temperature(temperature);
       }
    }
