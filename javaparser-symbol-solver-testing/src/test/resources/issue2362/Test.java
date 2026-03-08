public class Test
{
   public class InnerClass
   {
       public InnerClass(int i) {}
   }
    
   public Test() {
     new InnerClass(~8); 
   }
}