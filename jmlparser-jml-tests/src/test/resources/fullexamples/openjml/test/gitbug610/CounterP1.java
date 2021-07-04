public class CounterP1 {
    protected /*@ spec_public @*/ int count;
    public void inc() {
        count = count+1;
    }
    public /*@ pure @*/ int val() {
        return count;
    }
}
