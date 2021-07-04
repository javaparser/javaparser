// The complaint was that this did not prove. The problem is partly the specs and partly the code
// and partly handling of Strings.
public class buggyPalindrome
{
   private /*@ spec_public@*/String reverse = "";
   //@ public normal_behavior
   //@ assignable reverse;
   //@ ensures \result <==> reverse.equals(original);
   public boolean palindromeCheck(String original)
   {
      reverse = "";
      // @ assume \invariant_for(original);
      int length = original.length();
    
      //@ ghost int i_counter;
      //@ set i_counter = 0;
      //@ maintaining -1 <= i < original.length(); 
      //@ maintaining \forall int k; 0<=k<i_counter; reverse.charAt(k) == original.charAt(length-1-k);
      //@ decreases i;
      //@ maintaining reverse != null && reverse instanceof String && i_counter == reverse.length();
      //@ maintaining i_counter + i + 1 == length;
      // @ maintaining \invariant_for(reverse);
      for (int i = length - 1; i >= 0; i--){
          //@ assert \forall int k; 0<=k<i_counter; reverse.charAt(k) == original.charAt(length-1-k);
          //@ assert reverse.length() == i_counter;
         reverse = reverse + original.charAt(i);
         //@ assert reverse.length() == i_counter+1;
         //@ assert reverse.charAt(i_counter) == original.charAt(length-1-i_counter);
         //@ assert \forall int k; 0<=k<=i_counter; reverse.charAt(k) == original.charAt(length-1-k);
         // @ assert reverse.charAt(i_counter) == (original.charAt(reverse.length() - 1));
         //@ set i_counter = i_counter + 1;
       }
      //@ assert i_counter == length; 

         
      if (reverse.equals(original)){
         System.out.println("The string is a palindrome.");
     return true;
    }
      else{
         System.out.println("The string isn't a palindrome.");
     return false;
    }     
   }
   //@ assignable reverse;
   //@ ensures \result <==> reverse.equals(original);
   public boolean palindromeCheckExc(String original)
   {
      
       reverse = "";
       // @ assume \invariant_for(original);
      int length = original.length();
    
      //@ ghost int i_counter;
      //@ set i_counter = 0;
      //@ maintaining i >= -1 && i < original.length(); 
      //@ decreases i;
      //@ maintaining i_counter + i + 1 == length;
      for (int i = length - 1; i >= 0; i--){
         reverse = reverse + original.charAt(i-50); // Won't fail
         // assert original.charAt(i) == (reverse.charAt(reverse.length() - 1));
         //@ set i_counter = i_counter + 1;
       }
      //@ assert i_counter == length; 

         
      if (reverse.equals(original)){
         System.out.println("The string is a palindrome.");
     return true;
    }
      else{
         System.out.println("The string isn't a palindrome.");
     return false;
    }     
   }
   //@ public normal_behavior
   //@ assignable reverse;
   //@ ensures \result <==> reverse.equals(original);
   public boolean palindromeCheckCatch(String original)
   {
      
      int length = original.length();
    
      //@ ghost int i_counter;
      //@ set i_counter = 0;
      //@ maintaining i >= -1 && i < original.length(); 
      //@ decreases i;
      //@ maintaining i_counter + i + 1 == length;
      for (int i = length - 1; i >= 0; i--){
         reverse = reverse + original.charAt(i-50); // Fails
         //@ assume reverse instanceof String;
     // assert original.charAt(i) == (reverse.charAt(reverse.length() - 1));
     //@ set i_counter = i_counter + 1;
       }
      //@ assert i_counter == length; 

         
      if (reverse.equals(original)){
         System.out.println("The string is a palindrome.");
     return true;
    }
      else{
         System.out.println("The string isn't a palindrome.");
     return false;
    }     
   }
} 
