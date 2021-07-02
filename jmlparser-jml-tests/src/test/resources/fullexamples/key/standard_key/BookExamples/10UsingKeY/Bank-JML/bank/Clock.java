// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package bank;

/**
 * Singleton class for representing an assumed system-wide clock (for simplicity
 * we suppose that both the central host and all ATMs are running on the same
 * clock).
 * @stereotype singleton
 */
public class Clock {

    private /*@ spec_public @*/ static final Clock clockInstance = new Clock();    
    
    /**
     * The current date/time. We don't care about details of this representation
     * ...
     */
    private /*@ spec_public @*/ int currentDate = 0;
    
    /**
     * Private constructor as part of the applied singleton design pattern
     */
    private Clock() {}
    
    /**
     * @return Returns the instance.
     */
    /*@
        public normal_behavior
        ensures \result != null;
      @*/
    public /*@ pure @*/ static Clock getInstance () {
        return clockInstance;
    }

    /**
     * Make the time progress (don't care about overflows ...)
     */
    /*@
        public normal_behavior
        ensures clockInstance.currentDate > \old(clockInstance.currentDate);
        assignable clockInstance.currentDate;
      @*/
    public static void tick () {
        getInstance ().currentDate++;
    }
    
    /**
     * @return the current date/time
     */
    public /*@ pure @*/ static int getCurrentDate () {
        return getInstance ().currentDate;
    }
    
    /**
     * @return some date/time in a very distant past (used to initialise certain
     *         attributes in other classes)
     */
    public /*@ pure @*/ static int getBigBangsDate() {
        return -1000;
    }

    /**
     * @return <code>true</code> iff the two given dates refer to the same day
     */
    public /*@ pure @*/ static boolean isSameDay (int dateA, int dateB) {
        // dummy implementation
        return isSameInterval ( dateA, dateB, 10 );
    }

    /**
     * @return <code>true</code> iff <code>dateA</code> is an earlier date
     *         than <code>dateB</code>
     */
    public /*@ pure @*/ static boolean isEarlier (int dateA, int dateB) {
        return dateA < dateB;
    }
    
    /**
     * @return <code>true</code> iff the two given dates refer to the same day
     */
    /*@
        public normal_behavior
        ensures  isSameDay(dateA, dateB) ==> \result;
      @*/
    public /*@ pure @*/ static boolean isSameMonth (int dateA, int dateB) {
        // dummy implementation
        return isSameInterval ( dateA, dateB, 100 );
    }

    private /*@ pure @*/ static boolean isSameInterval (int dateA,
                                                        int dateB,
                                                        int intervalLength) {
        return dateA / intervalLength == dateB / intervalLength;
    }
}
