public interface Date {

   /*@ model instance int year ;
       model instance int month ;
       model instance int day ; @*/

    //@ ensures \result == this.month;
    /*@ pure @*/ int month();

    //@ ensures \result == this.day;
    /*@ pure @*/ int day();

    //@ ensures \result == this.year;
    /*@ pure @*/ int year();

    // Original submission had == instead of <==> 
    /*@ ensures \result <==> (this.year == birth.year) && this.month == birth.month && this.day == birth.day; @*/
   public /*@ pure @*/ boolean equals(Date birth);

}
