public class EscBits {
    
    public void m() {
        boolean b = true;
        boolean bb = false;
        //@ assert !(b & bb);
        //@ assert (b | bb);
        //@ assert !(b ^ bb);
        //@ assert (b & bb); // FALSE
    }
}