public class AgeBug implements Date { 

   private int _year; //@ in year;
   private int _month; //@ in month;
   private int _day; //@ in day;

   //@ private represents year = _year;
    //@ private represents month = _month;
    //@ private represents day = _day;

    //@ public invariant 1 <= year && year <= Integer.MAX_VALUE;
    //@ public invariant 1 <= month && month <= 12;
    //@ public invariant 1 <= day && day <= 31; 

    //@ requires 1 <= year && year <= Integer.MAX_VALUE;
    //@ requires 1 <= month && month <= 12;
    //@ requires 1 <= day && day <= 31;
    //@ ensures this.year == year;
    //@ ensures this.month == month;
    //@ ensures this.day == day;
    public /*@ pure @*/ AgeBug(int month, int day, int year) {
	this._month = month;
	this._day = day;
	this._year = year;
    }

   // specification inherited
   public /*@ pure @*/ int month() {
	return this._month;
   }

   // specification inherited
   public /*@ pure @*/ int day() {
	return this._day;
   }

   // specification inherited
   public /*@ pure @*/ int year() {
	return this._year;
   }

    // specification inherited
   public /*@ pure @*/ boolean equals(Date oth) {
        return _year == oth.year() && _month == oth.month() && _day == oth.day();
   }

   /*@ requires this != birth;
     @ ensures \result == ((this.year > birth.year) 
     @                   || (this.year == birth.year && this.month > birth.month) 
     @                   || (this.year == birth.year && this.month == birth.month && this.day > birth.day)); @*/
	public /*@ pure @*/ boolean today_later(AgeBug birth) {
		if (this._year != birth._year) {
			//@ assert true;
			return this._year > birth._year;
		} else if (this._month != birth._month) {
                        //@ assert this._year == birth._year;
			return this._month > birth._month;
		} else { 
                        //@ assert this._year == birth._year && this._month == birth._month;
			return this._day > birth._day;
		}
	}
   }
