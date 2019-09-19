public class Test
{
   public class InnerTest
   {
       public InnerTest() {}
   }
    
   public Test() {
   }

   public static void main( String[] args ) { 
       new Test().new InnerTest();
   }
}