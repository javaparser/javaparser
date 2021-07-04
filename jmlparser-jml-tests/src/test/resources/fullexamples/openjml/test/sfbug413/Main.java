interface X
{
    X m();
}

public class Main
{
    public static void main(String[] args)
    {
        // Do something that forces the inner class to be loaded
        new C();
        System.out.println("Done!");
    }

    public static class C implements X
    {
        @Override
        public C m()
        {
            return null;
        }
    }
}

// This bug resulted in a ClassFormat error on trying to run the rac-compiled program.
// The program was OK if C.m() returns an X instead of a C.