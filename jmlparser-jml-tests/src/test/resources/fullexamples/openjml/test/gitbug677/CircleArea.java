public class CircleArea{
    void lemma(int r) {
        //@ show r, 3*r, 3*r*r;
        //@ assert r > 0 && 3*r*r <= Integer.MAX_VALUE ==> 3*r <= Integer.MAX_VALUE;
    }
    
    //@ requires r > 0; 
    //@ requires 3*r*r <= Integer.MAX_VALUE;
    void calculateArea(int r)
    {
        //@ assert 3*r <= Integer.MAX_VALUE;
        //@ assert r*r <= Integer.MAX_VALUE;
        //@ show r, 3*r, 3*r*r;
        int area = 3*r*r;
    }

    //@ requires r > 0; 
    //@ requires 3*r*r <= Integer.MAX_VALUE;
    //@ @org.jmlspecs.annotation.Options("-code-math=java")
    void calculateAreaJava(int r)
    {
        int area = 3*r*r;
    }

    //@ requires r > 0; 
    //@ requires 3*r*r <= Integer.MAX_VALUE;
    //@ @org.jmlspecs.annotation.Options("-code-math=math")
    void calculateAreaMath(int r)
    {
        int area = 3*r*r;
    }
}
