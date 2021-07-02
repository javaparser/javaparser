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
 * Abstract superclass of all representatives of accounts, i.e. both the
 * permanent account objects <code>AccountData</code> and the temporary proxy
 * objects <code>OfflineAccountProxy</code>. This class provides
 * infrastructure for storing lists of transactions and some standard
 * implementations of account methods.
 */
public abstract class Account {

    /**
     * Account number of the account represented by <code>this</code> object
     * 
     * TODO: replace public with private; this seems to be a problem with the
     * JML-DL translation (accountNumber is not visible in JML specs for
     * subclasses if the Java visibility is private)
     */
    public final int accountNumber;
    
    //@ assignable this.accountNumber, this.transactions;
    protected Account (final int accountNumber) {
        this.accountNumber = accountNumber;
    }
    
    /**
     * Withdraw <code>amount</code> from the account
     * 
     * @param amount
     *            the amount to be withdrawn
     */
    /*@
        public normal_behavior
        requires   amount > 0;
        requires   newWithdrawalIsPossible(amount);
        ensures    balanceIsAccessible() ==>
                         accountBalance() == \old(accountBalance()) - amount;
        assignable transactions;
      @*/
    public abstract void withdraw (int amount);

    /**
     * Try to withdraw <code>amount</code> from the account with checking
     * whether this is possible, return the amount of money that is given out
     * 
     * @param amount
     *            the amount to be withdrawn
     * @return <code>amount</code> if the withdrawal was successful,
     *         <code>0</code> otherwise
     */
    /*@
        public normal_behavior
        requires   amount > 0;
        ensures    balanceIsAccessible() ==>
                         accountBalance() == \old(accountBalance()) - \result;
        ensures    \result == amount || \result == 0;
        assignable transactions;
      @*/
    public int checkAndWithdraw (int amount) {
        if ( newWithdrawalIsPossible ( amount ) ) {
//            System.out.println ( "Pay out " + amount );
            withdraw ( amount );
            return amount;
        } else {
//            System.out.println ( "Payment of " + amount + " rejected" );
            return 0;
        }
    }    

    /**
     * Request a printed account statement. This request may fail at a late
     * point if the account is offline, in this case nothing happens (the
     * customer does not receive anything). For this reason the method does not
     * have any preconditions
     */
    public abstract void requestStatement ();
    
    /**
     * @return <code>true</code> iff the balance of this account can be
     *         determined (not possible for the offline situation)
     */
    public /*@ pure @*/ abstract boolean balanceIsAccessible ();
    
    /**
     * @return the balance of this account
     */
    /*@
        public normal_behavior
        requires   balanceIsAccessible();
      @*/
    public /*@ pure @*/ abstract int accountBalance ();
    
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
        public normal_behavior
        requires amount > 0;
      @*/
    public /*@ pure @*/ abstract boolean newWithdrawalIsPossible (int amount);
    
    /**
     * @return the account number of the account represented by
     *         <code>this</code> object
     */
    /*@
        public normal_behavior
        ensures  \result == accountNumber;
      @*/
    public /*@ pure @*/ int getAccountNumber () {
        return accountNumber;
    }

    
    ////////////////////////////////////////////////////////////////////////////
    // Storage of transactions
    ////////////////////////////////////////////////////////////////////////////
    
    /**
     * A list of transactions in which the most recent transaction is the first
     * element
     */
    public /*@ spec_public @*/ TransactionList transactions =
        TransactionList.EMPTY_LIST;
    
    /**
     * Add a transaction <code>trance</code> to the list of stored transaction
     * 
     * @param trance
     *            the transaction to be added
     */
    /*@
        protected normal_behavior
        assignable transactions;
      @*/
    protected void addTransaction (Transaction trance) {
        transactions = transactions.prepend ( trance );
    }
    
    /**
     * Get all transactions that have been performed for this account. In the
     * resulting list, the most recent transaction is the first element.
     * 
     * @return the list of transactions
     * 
     * @stereotype query
     */
    protected /*@ pure @*/ TransactionList getTransactions () {
        return transactions;
    }

    /**
     * Remove all transactions that have been pushed using
     * <code>addTransaction</code>
     */
    protected void flushTransactions () {
        transactions = TransactionList.EMPTY_LIST;
    }

    /**
     * Helper method, used by the two subclasses of this class for implementing
     * <code>toString</code>
     * 
     * @return the linearised result of <code>getTransactions</code>
     */
    protected /*@ pure @*/ String transactionListToString () {
        final StringBuffer res = new StringBuffer ();
        TransactionList transes = getTransactions ();
        while ( !transes.isEmpty () ) {
            res.append ( "" + transes.head () );
            transes = transes.tail ();
            if ( !transes.isEmpty () ) res.append ( ", " );
        }
        return res.toString ();
    }
}
