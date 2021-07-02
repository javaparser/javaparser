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
 * Class for representing accounts in an ATM that is switched offline. All
 * transactions are buffered in this situation and can later be replayed to copy
 * them to the actual account. The class realises a limit of 1000 bucks that can
 * at most be withdrawn before transactions have to be replayed to the permanent
 * account. Objects of this class are created when an account is accessed for
 * the first time at an offline ATM and are deleted once the ATM gets online
 * again
 */
public class OfflineAccountProxy extends Account {

    private /*@ spec_public @*/ static final int sessionLimit = 1000;

    /**
     * The remaining amount of money that can be withdrawn using this account
     * representation before a synchronisation with the permanent account
     * storage becomes necessary
     */
    //@ private invariant offlineBalance >=0 && offlineBalance <= 1000;
    private /*@ spec_public @*/ int offlineBalance = sessionLimit;    

    public /*@ pure @*/ OfflineAccountProxy (int accountNumber) {
        super ( accountNumber );
    }

    /**
     * Withdraw <code>amount</code> from the account
     * 
     * @param amount
     *            the amount to be withdrawn
     */
    /*@
        also
      
        public normal_behavior
        requires   amount > 0;
        requires   newWithdrawalIsPossible(amount);
        ensures    balanceIsAccessible() ==>
                         accountBalance() == \old(accountBalance()) - amount;
        assignable offlineBalance;
      @*/
    public void withdraw (int amount) {
        addTransaction ( new Withdrawal ( Clock.getCurrentDate(), amount ) );
        offlineBalance -= amount;
    }

    /**
     * Request a printed account statement. This request may fail at a late
     * point if the account is offline, in this case nothing happens (the
     * customer does not receive anything). For this reason the method does not
     * have any preconditions
     */
    public void requestStatement () {
        addTransaction ( new AccountStatementRequest ( Clock.getCurrentDate () ) );
    }

    /**
     * @return <code>true</code> iff the balance of this account can be
     *         determined (not possible for the offline situation)
     */
    public /*@ pure @*/ boolean balanceIsAccessible () {
        return false;
    }

    /**
     * @return the balance of this account
     */
    /*@
        also
       
        public normal_behavior
        requires   balanceIsAccessible();
        ensures    false;
      @*/
    public /*@ pure @*/ int accountBalance () {
        throw new RuntimeException ();
    }
    
    /**
     * Determine whether a certain amount of money may be withdrawn. Using
     * method <code>PermanentAccount.withdraw(int,int)</code> it is possible to
     * circumvent this check, which is necessary because for offline withdrawals
     * the balance cannot be accessed and checked
     * 
     * @param amount
     *            the amount of money requested
     * @return <code>true</code> iff <code>amount</code> can be withdrawn
     *         from the account
     */
    /*@
        also
       
        public normal_behavior
        requires amount > 0;
     @*/
    public /*@ pure @*/ boolean newWithdrawalIsPossible (int amount) {
        return amount <= offlineBalance;
    }
    
    /**
     * Make the transactions buffered in <code>this</code> object persistent
     * by copying them to a permanent account
     * 
     * @param target
     *            the account the transactions are supposed to be copied to
     */
    public void replay (PermanentAccount target) {
        // replay transactions in the right order
        replay ( target, getTransactions () );
        flushTransactions ();
    }

    /**
     * Recursive helper method for replaying transactions
     * 
     * @param target
     *            the account the transactions are supposed to be copied to
     * @param transes
     *            list of transactions that should be replayed
     */
    private void replay (PermanentAccount target, TransactionList transes) {
        if ( transes.isEmpty () ) return;
        replay ( target, transes.tail () );
        transes.head ().replay ( target );
    }
}
