public class TestRefinesBad {
    
    public int mbad(int i) {
        
        int j;
        //@ begin
        j = i + 10;
        j++;
        return j;
    }
    public int mbad2(int i) {
        
        int j;
        //@ end
        j = i + 10;
        j++;
        return j;
    }
    public int mbad4(int i) {

        int j;
        //@ refining ensures true;
        //@ begin
        return j;
    }

    public int mbad5(int i) {

        int j;
        //@ refining ensures true;
        j += 10;
        //@ end
        return j;
    }

    public void mbad6(int i) {

        int j;
        //@ refining ensures true;
    }
}