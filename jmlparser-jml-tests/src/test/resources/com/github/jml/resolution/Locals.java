public class Locals {
    public void foo() {
        int local = 0;
        //@ ghost int jmlLocal = local;
        //@ assert jmlLocal == 0;
        local = jmlLocal;
        //! java2jml: jmlLocal @ (line 6,col 17)
    }
}