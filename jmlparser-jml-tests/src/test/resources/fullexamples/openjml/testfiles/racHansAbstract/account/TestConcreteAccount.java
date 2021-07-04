package account;

import org.jmlspecs.utils.JmlAssertionError;

import unitTest.TestCase;

public class TestConcreteAccount extends TestCase
{

  public static void main(String ... args) {
    int k = args.length == 0 ? 10 : Integer.parseInt(args[0]);
    new TestConcreteAccount("T").test(k);
  }

  public TestConcreteAccount(String name)
  {
    super(name);
  }
  
  public void test (int i) 
  { 
    switch (i) { 
      case 1:
        new ConcreteAccount(0); break; 
//      case 2:
//        new ConcreteAccount(100); break;
//      case 3: 
//        try { new ConcreteAccount(-1); assert false; }
//        catch (JmlAssertionError e){}; break;
//      
//      case 4: 
//        new ConcreteAccount(100).balance(); 
//        break;
//      case 5: 
//        new ConcreteAccount(0).balance();  
//        break;
//      case 6:
//        AbstractAccount acc = new ConcreteAccount(300);
//        assert acc.balance() == 300;
//        break;
      default: break;
    }
  }
  
  public static final int testCount = 9; 
}
