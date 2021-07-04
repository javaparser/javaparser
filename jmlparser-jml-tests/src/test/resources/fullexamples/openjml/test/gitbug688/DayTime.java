public class DayTime {

    /*@ spec_public @*/ private int seconds;
    /*@ spec_public @*/ private int minutes;
    /*@ spec_public @*/ private int hours;

	//@ public invariant 0 <= seconds && seconds < 60;
	//@ public invariant 0 <= minutes && minutes < 60;
	//@ public invariant 0 <= hours && hours < 24; 


    //@ requires 0 <= hours && hours < 24;
    //@ requires 0 <= minutes && minutes < 60;
    //@ requires 0 <= seconds && seconds < 60;
    //@ ensures this.hours == hours;
    //@ ensures this.minutes == minutes;
    //@ ensures this.seconds == seconds;
    //@ pure
    public DayTime(int hours, int minutes, int seconds) {
	this.seconds = seconds;
	this.minutes = minutes;
	this.hours = hours;
    }

   //@ ensures \result == this.hours;
   public /*@ pure @*/ int hour() {
	return this.hours;
   }

   //@ ensures \result == this.minutes;
   public /*@ pure @*/ int minute() {
	return this.minutes;
   }

   //@ ensures \result == this.seconds;
   public /*@ pure @*/ int second() {
	return this.seconds;
   }


    //@ ensures \result == (a.hours*3600) + (a.minutes*60) + a.seconds;
    private /*@ pure spec_public@*/ int secondCalulation(DayTime a) {
	return (a.hours*3600) + (a.minutes*60) + a.seconds;
    }
 	

    //@ old int diff = secondCalulation(this) - secondCalulation(stop);
    //@ old int _final = (diff < 0) ? (-diff) : (diff);
    //@ ensures \result == _final;
    public /*@ pure @*/ int diffSeconds(DayTime stop){
	int diff = secondCalulation(this) - secondCalulation(stop);
	if(diff < 0)
		return -diff;
	else
		return diff;
    }
}
