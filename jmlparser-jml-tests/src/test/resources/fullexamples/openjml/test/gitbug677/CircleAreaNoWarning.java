public class CircleAreaNoWarning{
    //@ requires r > 0; 
    //@ requires 3*r*r <= Integer.MAX_VALUE;
    void calculateAreaNoWarning(int r)
    {
        int area = 3*(r*r);
    }
}
