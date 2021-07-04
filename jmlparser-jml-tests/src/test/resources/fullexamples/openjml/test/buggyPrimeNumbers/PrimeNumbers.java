//Printing first n prime numbers
    
    public class PrimeNumbers
    {
        //@ public normal_behavior     
        //@ requires d != 0;
	// ensures \result == true ==> n%d == 0;        // this post condition is time consuming.
        //@ pure function
        public static boolean div(int n, int d) { return n%d == 0; }

        private /*@ spec_public nullable @*/ int primeArray[];
        //@ requires 1 <= n && n < Integer.MAX_VALUE;
        //@ assignable primeArray;
        //@ ensures primeArray.length == n;
        //@ ensures (\forall int i, j; 0 <= i && i < primeArray.length && 2 <= j && j <= primeArray[i]/2; !div(primeArray[i],j));
	//@ ensures (\forall int i,j; 0 <= i && i < primeArray.length && 0 <= j && j < primeArray.length && i != j; primeArray[i] != primeArray[j]);
        public void Prime(int n)
       {
          int status = 1, num = 3, count, j;
          primeArray = new int[n];
          
          if (n >= 1)
          {
             System.out.println("First "+n+" prime numbers are:");
             System.out.println(2);
             primeArray[0] = 2;
          }
	 //@ assert num == 3;
	 //@ assert primeArray[0] == 2;
	 //@ assert num != primeArray[0];
         //@ ghost int maxnumber = Integer.MAX_VALUE;
	 //@ ghost int count_counter = 2;

         //@ maintaining (\forall int i, k; 0 <= i && i < count-1 && 2 <= k && k <= primeArray[i]/2; !div(primeArray[i],k));
          //@ maintaining (\forall int i, k; 0 <= i && i < count-1 && 0 <= k && k < count-1 && i != k; primeArray[i] != primeArray[k]);
          //@ maintaining (\forall int i; 0 <= i && i < count-1; primeArray[i] < num); // Added this line to Amirfarhad's submission
         //@ maintaining num >= 3;
         //@ maintaining count >= 2 && count <= n + 1;
	 //@ maintaining count_counter == count;
	 //@ loop_invariant status == 1;
         //@ decreases maxnumber - num;
          for (count = 2; count <= n;)
          { 
	     
             //@ maintaining j> 1 && j <= num/2 + 1;
	     //@ maintaining status == 1;
	     //@ maintaining (\forall int k; 0 <= k && k < count - 1; num != primeArray[k]);
	     //@ maintaining (\forall int k; 2 <= k && k < j; !div(num,k));
             //@ decreases num - j;
             for (j = 2; j <= num/2; j++)
             { 
                if (div(num,j))
                {
                   //@ assert div(num,j);
                   status = 0;
                   break;
                }
                //@ assert !div(num,j);
             }

             if (status != 0)
             {  
                //@ assert status != 0;
                primeArray[count -1] = num;
		//@ assert (\forall int k; 0 <= k && k < count - 1; num != primeArray[k]);
                //@ assert (\forall int i; i >= 2 && i <= num/2; !div(num,i));
		//@ assert primeArray[count -1] == num;
                System.out.println("prime is : "+num); 
                count++;
		//@ set count_counter = count_counter + 1;
             }
	    
             status = 1;
	     //@ assume num < Integer.MAX_VALUE;
             num++;
          }  
       }
    }
