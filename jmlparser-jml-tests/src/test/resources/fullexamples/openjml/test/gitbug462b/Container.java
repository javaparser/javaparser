public class Container {
    private /*@ spec_public @*/ int a;

    /*@ private normal_behavior
      @   assignable \nothing;
      @   ensures true;
      @*/
    private /*@ helper @*/ Container() {}

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result.a == 127; 
      @*/
    public static /*@ pure @*/ Container allocate() {
        Container c = new Container();
        c.a = 127;
        return c;
    }

    /*@ also public normal_behavior
      @   assignable \nothing;
      @   ensures \result <==> (obj instanceof Container) && ((Container) obj).a == a;
      @*/
    public /*@ pure @*/ boolean equals(Object obj) {
        return (obj instanceof Container) && ((Container) obj).a == a;
    }
    
    public static class ContainerUser {
        private /*@ spec_public non_null @*/ Container c;

        /*@ private normal_behavior
          @   assignable \nothing;
          @   ensures true;
          @*/
        private /*@ helper @*/ ContainerUser() { c = new Container(); }

        /*@ public normal_behavior
          @   assignable \nothing;
          @   //ensures Container.allocate() instanceof Container;
          @   ensures \result.c.equals(Container.allocate());
          @   // edit: turning this around into "Container.allocate().equals(\result.c)" does
          @   // establish that \result.c is an instance of Container, but the type system and
          @   // fact that \result.c != null should already establish this
          @*/
        public static ContainerUser allocate() {
            ContainerUser user = new ContainerUser();
            user.c = Container.allocate();
            return user;
        }

        public void test() {
            ContainerUser user = allocate();
            Container cont = Container.allocate();
            //@ assert user instanceof ContainerUser; // passes
            //@ assert cont instanceof Container;     // passes
            //@ assert user.c.a == 127;               // passes
            //@ assert user.c instanceof Container;   // fails - fixed
        }
    }
} 
// The original buggy example surfaced two problems:
// 1) assignment to user.c was not allowed, even though user was a fresh object
// 2) user.c could not be shown to have type Container, even though it is declared to be that type
