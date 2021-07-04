//Printing first n prime numbers
     
    public class PrimeNumbers
    {
	private /*@ spec_public nullable@*/ int primeArray[];
	//@ requires 1 <= n < Integer.MAX_VALUE;
	//@ assignable primeArray;
	//@ ensures primeArray != null;
	//@ ensures primeArray.length == n;
	//@ ensures (\forall int i, j; i >= 0 && i < primeArray.length && j >= 2 && j <= primeArray[i]/2; primeArray[i]%j != 0); 
	public void Prime(int n)
       {
          int status = 1, num = 3, count, j =2;
          primeArray = new int[n];
          if (n >= 1)
          {
             primeArray[0] = 2;
          }
          //@ ghost int maxnumber = Integer.MAX_VALUE;

          //@ maintaining 2 <= count <= n + 1; 
          //@ maintaining primeArray[count-2] < num <= maxnumber;
          //@ maintaining status == 1;
          //@ maintaining (\forall int i, k; 0 <= i < count-1 && 2 <= k <= primeArray[i]/2; primeArray[i]%k != 0); 
          //@ decreases maxnumber - num; 
          //@ split
          for (count = 2; count <=n && num < Integer.MAX_VALUE;)
          {    
              //@ maintaining 2 <= j <= num/2 + 1; 
              //@ maintaining status != 0 && (\forall int jj; 2 <= jj <= j; num%jj != 0);
              //@ decreases num - j;
              for (j = 2; j <= num/2; j++)
              {
                  if (num%j == 0)
                  {
                      //@ assert num%j == 0;
                      status = 0;
                      break;
                  }
                  //@ assert num%j != 0;
              }
              //@ assert status == 0 ==> (\exists int jj; 2 <= jj <= num/2; num%jj == 0);
              //@ assert status != 0 ==> (\forall int jj; 2 <= jj <= num/2; num%jj != 0);

              if (status != 0)
              {
                  primeArray[count-1] = num;
                  //@ assert (\forall int i; 2 <= i <= num/2; num%i != 0);
                  count++;
              }
              status = 1;
              num++;
          }   
          //@ assume count == primeArray.length + 1;
       }
    }
