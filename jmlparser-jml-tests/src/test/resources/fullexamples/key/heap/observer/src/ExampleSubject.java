public class ExampleSubject extends Subject {
    private int value;

    //@ represents footprint = \locset( value );

    /*@ public normal_behaviour
      @   ensures \fresh(footprint);
      @   ensures observers != null && \fresh(observers) && observers.length == 0;
      @*/
    public /*@pure@*/ ExampleSubject() {
        value = 33;
    }


    /*@ normal_behaviour
      @  accessible footprint;
      @  ensures \result == value();
      @*/
    public /*@pure helper@*/ int value() {
        return value;
    }


    /*@ public normal_behaviour
      @   assignable footprint;
      @   ensures footprint == \old(footprint);
      @*/
    public void change() {
        value += 981;
    }
}
