public class Container {
    /*@ private normal_behavior
      @   assignable \nothing;
      @*/
    private /*@ helper @*/ Container() {}

    /*@ public normal_behavior
      @   assignable \nothing;
      @*/
    public static /*@ pure @*/ Container allocate() {
        Container c = new Container();
        return c;
    }
    
    public static class ContainerUser {
        public /*@ non_null @*/ Container c;

        /*@ private normal_behavior
          @   assignable \nothing;
          @*/
        private /*@ helper @*/ ContainerUser() { c = new Container(); }

        /*@ public normal_behavior
          @   assignable \nothing;
          @*/
        public static ContainerUser allocate() {
            ContainerUser user = new ContainerUser();
            user.c = Container.allocate();
            return user;
        }
    }
}