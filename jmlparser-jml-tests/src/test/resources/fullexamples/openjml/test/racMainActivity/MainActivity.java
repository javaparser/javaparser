// Calculator-JML program by Pushkar Ogale
// CS 5374 Fall 2013
// NOTE: Added as a test case because it crashed (with RAC) under 12/12 release
import java.io.*;
import java.util.*;
import java.math.*;

//import java.lang.*;


public class MainActivity {

	public static double Res=0; //Global Result variable
	public static double ResS=0; //Global Result variable
	public static double ResM=0; //Global Result variable
	public static double ResSu=0; //Global Result variable
	public static double ResD=0; //Global Result variable
	public static double ResH=0; //Global Result variable
	public static double ResP=0; //Global Result variable
	double I1, I2, result;
	
	//Thread to process Sum
	//@ requires I1 >= 0 && I2>=0;
	//@ ensures \result > 0.0;

	public static double SumThread(double I1, double I2)
	{			  	
		
		if ((I1>0) && (I2>0))
			ResS=I1+I2;
		else
			ResS=0;
		return(ResS);						
	}
			//Thread to process Division	

	//@ requires I2 > 0;
	//@ ensures \result < 0;
	public static double DivThread(double I1, double I2)
	{
		ResD=I1/I2;	
		return(ResD);			
	}
			//Thread to process Subtract

	//@ requires I1 > I2;
	//@ ensures \result > 0;
	public static double DiffThread(double I1, double I2)
	{
		 if (I1 > I2)
			ResSu=I1-I2;
		else
			ResSu=0;
		  return(ResSu);			
	 }			
			//Thread to process Multiplication
	//@ requires I1 > 0 && I2 > 0;
	//@ ensures \result >0;
	public static double MultThread(double I1, double I2)
	{
		 if ((I1>0) && (I2>0))
			ResM=I1*I2;
		else
			ResM=0;
		  return(ResM);			   
	}

	//@ requires I1 > 0 && I2 > 0;
	//@ ensures \result > 0;
	
	public static double HypotThread(double I1, double I2)
	{
		if ((I1>0) && (I2>0))
			ResH=Math.sqrt(Math.pow(I1,2)+Math.pow(I2,2));
		else
			ResH = 0;
		// @ ensures \result > 0; // TODO: Avoid crash when this is enabled
		 return(ResH);			   
	}
	

	//@ requires I1 > 0 && I2 >= 0 ;
	//@ ensures \result >0;
	public static double PowThread(double I1, double I2)
	{
		if ((I1>0) && (I2>0))
			ResP=Math.pow(I1,I2);
		else
			ResP = 0;	
		  return(ResP);			   
	}
			
	public static void main(String [] args) throws IOException {
		boolean loopcheck=true;
		boolean loopcheck2=true;
		double iet1=0,iet2=0;
		String s;
		char c;
		
		BufferedReader stdin=new BufferedReader (new InputStreamReader (System.in));			
		Scanner stdin2 = new Scanner(System.in);
		
		while (loopcheck==true)
		{
			System.out.println();  
		    System.out.print("Enter Number1: ");
		    	// Read user input			
		    iet1=stdin2.nextDouble();
		    System.out.println();
		   	System.out.print("Enter Number2: ");
		   	iet2=stdin2.nextDouble();
			System.out.println();
			
		   		
		   	while (loopcheck2 == true)
		   	{
		   		System.out.println("\t Enter your choice of operation on the 2 numbers: \n\n"
		   										+"\t A to ADD:\n"
		   										+"\t S to Subtract: \n"
		   										+"\t M to Multiply: \n"
		   										+"\t D to Divide: \n"
												+"\t H for Hypotenuse: \n"
												+"\t P for Power function: \n"
		   										+"\t or Q to quit: \n");
		   		System.out.println();
		   		// Read user input code			
		   		s=stdin.readLine();//.charAt(0);
		   		System.out.flush();
		   		if (s.length() == 0) {
		   			System.out.println("Exiting, you hit Enter");
		   			System.exit(0);
		   		}

		   		c=s.charAt(0);
		   		//System.out.println("User input is : "+c); //Debug statement

		   		// 
		   		switch(c)
		   		{					
		   			case 'A':
		   			{
		   					Res= SumThread(iet1,iet2);
		   					System.out.println("Sum is: " + Res);
		   					System.out.println();
		   					break;
		   			}

		   			case 'M':
		   			{
		   					Res = MultThread(iet1,iet2);									
		   					System.out.println("Product is: " + Res);
		   					System.out.println();
		   					break;

		   			}

		   			case 'S':
		   			{
		   				Res= DiffThread(iet1,iet2);
		   				System.out.println("Difference is: " + Res);
		   				System.out.println();
		   				break;
		   			}

		   			case 'D':
		   			{			
		   				Res=DivThread(iet1,iet2);
		   				System.out.println("Quotient is: " + Res);
		   				System.out.println();
		   				break;
		   			}

					case 'H':
		   			{			
		   				Res=HypotThread(iet1,iet2);
		   				System.out.println("Hypotenuse is: " + Res);
		   				System.out.println();
		   				break;
		   			}

					case 'P':
		   			{			
		   				Res=PowThread(iet1,iet2);
		   				System.out.println("Power Result is: " + Res);
		   				System.out.println();
		   				break;
		   			}

		   			case 'Q':
		   			{
		   				System.out.println("Quitting");
		   				System.out.println();
		   				loopcheck2=false;
		   				loopcheck=false;
		   				break;
		   			}
			
		   			default:
		   			{
		   				System.out.println("Invalid Choice Try Again");	
		   				System.out.println();
		   				break;
		   			}
		   		}
		   	}
		}
	   return;	
	}		  
}