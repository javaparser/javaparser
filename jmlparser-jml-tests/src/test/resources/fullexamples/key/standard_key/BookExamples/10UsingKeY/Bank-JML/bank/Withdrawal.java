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
 * Class for representing the transaction kind withdrawal, i.e. the act of
 * withdrawing a certain amount of money from an account.
 * Objects of this class are immutable
 */
public class Withdrawal extends Transaction {
    
    /**
     * The amount of money that is withdrawn
     */
    //@ public invariant amount > 0;
    private /*@ spec_public @*/ final int amount;

    /*@
        public normal_behavior
        requires  amount > 0;
      @*/
    public /*@ pure @*/ Withdrawal (final int date, final int amount) {
        super ( date );
        this.amount = amount;        
    }

    /**
     * The design pattern "Strategy" is used for implementing the
     * synchronisation of offline account proxies with the permanent accounts.
     * Invoking this method carries out <code>this</code> transaction on the
     * real account. Note that the withdrawal from the permanent account is
     * performed for the correct date
     * 
     * @param target
     *            the permanent account on which <code>this</code> transaction
     *            is supposed to be carried out
     */
    public void replay (PermanentAccount target) {
        target.withdraw ( getDate (), getAmount () );
    }

    /**
     * @return the amount of money that is withdrawn
     */
    public /*@ pure @*/ int getAmount () {
        return amount;
    }

    
    public /*@ pure @*/ String toString () {
        return "" + getDate() + ":Withdrawal: " + getAmount();
    }
}
