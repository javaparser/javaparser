package core;

public class Student {
    /*@ public invariant
      @  matrNr>0 && firstname != null && surname != null;
      @*/

    public final int matrNr;
    public final String firstname;
    public final String surname;

    public int points;
    public int bonusPoints;
    public boolean backedOut; 

    public Student(int matrNr, String firstname, String surname){
	this.matrNr = matrNr;
	this.firstname = firstname;
	this.surname = surname;
	points = -1;
        bonusPoints = 0;
	backedOut = false;
    }
}
