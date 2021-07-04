public interface Middle extends Top {
    /*@ public normal_behavior
      @   ensures \result == 4;
      @*/
    public int other();
}