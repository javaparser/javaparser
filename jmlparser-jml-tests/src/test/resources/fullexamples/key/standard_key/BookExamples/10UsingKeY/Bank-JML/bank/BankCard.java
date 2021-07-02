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
 * Class for representing bank cards. The class provides attributes for the PIN
 * of the card (abstracting from any kind of more advanced PIN storage concept)
 * and the account number. Cards can be invalidated by ATMs (used when cards are
 * confiscated), which is simulated using a boolean attribute.
 */
public class BankCard {

    /**
     * The correct PIN that needs to be entered when using <code>this</code>
     * card
     */
    private /*@ spec_public @*/ final int correctPIN;
    
    /**
     * The account related to <code>this</code> card
     */
    private /*@ spec_public @*/ final int accountNumber;
    
    /**
     * This attribute is <code>true</code> iff the card represented by this
     * object is has been deactivated
     */
    private /*@ spec_public @*/ boolean invalid = false;
    
    public /*@ pure @*/ BankCard (final int accountNumber, final int correctPIN) {
        this.correctPIN = correctPIN;
        this.accountNumber = accountNumber;
    }
    
    /**
     * Determine whether a given PIN is correct for this card. For invalid
     * cards, this check always returns <code>false</code>
     * 
     * @param pin
     *            the PIN that is supposed to be check
     * @return <code>true</code> iff <code>pin</code> is correct and the
     *         card is valid
     */
    /*@
        public normal_behavior
        ensures  \result <==> !invalid && pin == correctPIN;
      @*/
    public /*@ pure @*/ boolean pinIsCorrect (int pin) {
        if ( cardIsInvalid () ) return false;
        return correctPIN == pin;
    }
    
    /**
     * Invalidate a card
     */
    /*@
        public normal_behavior
        ensures  invalid;
        assignable invalid;
      @*/
    public void makeCardInvalid () {
        invalid = true;
    }
    
    /**
     * @return <code>true</code> iff <code>this</code> card is invalid
     */
    /*@
        public normal_behavior
        ensures  \result == invalid;
      @*/
    public /*@ pure @*/ boolean cardIsInvalid () {
        return invalid;
    }
    
    /**
     * @return the account number of the account related to this card
     */
    /*@
        public normal_behavior
        ensures  \result == accountNumber;
      @*/
    public /*@ pure @*/ int getAccountNumber () {
        return accountNumber;
    }

}
