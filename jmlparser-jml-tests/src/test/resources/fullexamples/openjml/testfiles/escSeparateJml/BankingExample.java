
public class BankingExample
{

   public static final int MAX_BALANCE = 1000; 
   private int balance;
   private boolean isLocked = false; 

   
   public BankingExample()
   {
       this.balance = 0;
   }

   
   public void credit(final int amount)
   {
       this.balance += amount;
   }

   
   public void debit(final int amount)
   {
       this.balance -= amount;
   }

  
   public void lockAccount()
   {
       this.isLocked = true;
   }

   
   public int getBalance() throws Exception
   {
       if (!this.isLocked)
       {
               return this.balance;
       }
       else
       {
               throw new Exception();
       }
   }
}
