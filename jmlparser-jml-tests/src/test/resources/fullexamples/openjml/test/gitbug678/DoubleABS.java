public class DoubleABS{  
    //@ requires !num.isNaN() && num >= 0;
    //@ ensures \result == num;
    //@ ensures \result >= 0;

    //@ also

    //@ requires !num.isNaN() && num < 0;
    //@ ensures \result == -num; 
    //@ ensures \result >= 0;
    public /*@ pure @*/ Double DoubleAbsolute(Double num){
        if (num >= 0)
            return num;
        else
            return -num;
    } 
}
