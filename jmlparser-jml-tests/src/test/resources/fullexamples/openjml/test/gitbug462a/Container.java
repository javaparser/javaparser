public class Container {
    /*@ private normal_behavior
      @   assignable \nothing;
      @*/
    private /*@ helper @*/ Container() {}

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \fresh(\result);
      @*/
    public static /*@ pure @*/ Container allocate() {
        Container c = new Container();
        return c;
    }
    
    public static class ContainerUser {
        public void test() {
            Container c = Container.allocate();
        }
    }
}