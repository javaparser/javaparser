public class CantCompileRAC
{ 
  public static void main(final String[] the_args)
  {  
    Throwable t = new Throwable();
    t.getStackTrace();
  }
}
