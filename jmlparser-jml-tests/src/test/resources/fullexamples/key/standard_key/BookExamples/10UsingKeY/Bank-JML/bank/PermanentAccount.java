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
 * Permanent representation of information about an account. Non-essential
 * information like the customer to which an account belongs is not modelled
 * here. The class implements a daily limit of 1000 somethings (which can only
 * be enforced if employed ATMs are online, however) and one free account
 * statement a month. It is possible that the <code>balance</code> of
 * represented accounts is negative, which cannot be sidestepped because the
 * possibility of offline withdrawals is mandatory
 */
public class PermanentAccount extends Account {

    private /*@ spec_public @*/ static final int dailyLimit = 1000;

    /**
     * Balace of this account
     */
    private /*@ spec_public @*/ int balance;
    
    /**
     * The time/date of the latest withdrawal. This information is used to
     * ensure that not more than 1000 units are withdrawn per day
     */
    private /*@ spec_public @*/ int dateOfLatestWithdrawal = Clock.getBigBangsDate ();
    
    /**
     * The amount of money that has been withdrawn so far on the day
     * <code>dateOfLatestWithdrawal</code>
     */
    //@ private invariant amountForLatestWithdrawalDay >= 0;
    private /*@ spec_public @*/ int amountForLatestWithdrawalDay = 0;
    
    /**
     * The latest date at which an account statement was sent to the customer 
     */
    private int dateOfLatestAccountStatement = Clock.getBigBangsDate ();

    public /*@ pure @*/ PermanentAccount (int accountNumber, int balance) {
        super ( accountNumber );
        this.balance = balance;
    }

    /**
     * Withdraw <code>amount</code> from the account
     * 
     * TODO: should the premiss "clock.isEarlier(clock.instance.currentDate,
     * dateOfLatestWithdrawal)" rather be made some kind of invariant?
     * 
     * @param amount
     *            the amount to be withdrawn
     */
    /*@
        also
       
        public normal_behavior
        requires  amount > 0;
        requires  newWithdrawalIsPossible(amount);
        ensures   balance == \old(balance) - amount;
        assignable balance, dateOfLatestWithdrawal, amountForLatestWithdrawalDay;

        also
        
        public normal_behavior
        requires  amount > 0;
        requires  newWithdrawalIsPossible(amount);
        requires  !Clock.isEarlier(Clock.clockInstance.currentDate,
                                   dateOfLatestWithdrawal);
        requires  !Clock.isSameDay(Clock.clockInstance.currentDate,
                                   dateOfLatestWithdrawal);
        ensures   amountForLatestWithdrawalDay == amount;
        assignable balance, dateOfLatestWithdrawal, amountForLatestWithdrawalDay;
                        
        also
        
        public normal_behavior
        requires  amount > 0;
        requires  newWithdrawalIsPossible(amount);
        requires  !Clock.isEarlier(Clock.clockInstance.currentDate,
                                   dateOfLatestWithdrawal);
        requires  Clock.isSameDay(Clock.clockInstance.currentDate,
                                  dateOfLatestWithdrawal);
        ensures   amountForLatestWithdrawalDay ==
                        \old(amountForLatestWithdrawalDay) + amount;        
        assignable balance, dateOfLatestWithdrawal, amountForLatestWithdrawalDay;
      @*/
    public void withdraw (int amount) {
        withdraw ( Clock.getCurrentDate (), amount );
    }

    /**
     * Request a printed account statement. This request may fail at a late
     * point if the account is offline, in this case nothing happens (the
     * customer does not receive anything). For this reason the method does not
     * have any preconditions
     */
    public void requestStatement () {
        requestStatement ( Clock.getCurrentDate () );
    }

    /**
     * @return <code>true</code> iff the balance of this account can be
     *         determined (not possible for the offline situation)
     */
    public /*@ pure @*/ boolean balanceIsAccessible () {
        return true;
    }

    /**
     * @return the balance of this account
     */
    /*@
        also
       
        public normal_behavior
        requires  balanceIsAccessible();
      @*/
    public /*@ pure @*/ int accountBalance () {
        return balance;
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
        return amount <= accountBalance ()
               && amount <= dailyLimit - getWithdrawnAmountForToday ();
    }

    /**
     * Withdraw <code>amount</code> from the account and record this
     * transaction for the date <code>date</code>. This method is used by
     * <code>Transaction.replay</code> and can lead to negative account
     * balances and violations of the daily limit
     * 
     * @param amount
     *            the amount to be withdrawn
     * @param date
     *            the date for the transactions should be recorded
     * 
     * TODO: specify modification of daily limit counter ...
     */
    /*@
        normal_behavior
        requires  amount > 0;
        ensures   balance == \old(balance) - amount;
        assignable balance, dateOfLatestWithdrawal, amountForLatestWithdrawalDay;
      @*/
    void withdraw (int date, int amount) {
        addTransaction ( new Withdrawal ( date, amount ) );
        
        // TODO: this might lead to negative balances ...
        balance -= amount;
    
        if ( dailyLimitIsImportant ( date ) )
            amountForLatestWithdrawalDay += amount;
    }

    /**
     * Determine whether for a withdrawal at (past) date <code>date</code> the
     * attribute <code>amountForLatestWithdrawalDay</code> that implements the
     * daily limit has to be updated. This is not the case if at days later than
     * <code>date</code> withdrawals have been performed in the meantime
     * 
     * TODO: here a nice specification seems possible ...
     * 
     * @param date
     *            day that is supposed to be checked
     * @return <code>true</code> iff the attribute
     *         <code>amountForLatestWithdrawalDay</code> should be updated
     */
    /*@
        private normal_behavior
        assignable dateOfLatestWithdrawal, amountForLatestWithdrawalDay;
      @*/
    private boolean dailyLimitIsImportant (int date) {
        if ( Clock.isSameDay ( date, dateOfLatestWithdrawal ) )
            // recent withdrawal and not the first for this day ...
            return true;
        if ( Clock.isEarlier ( date, dateOfLatestWithdrawal ) )
            // withdrawal for a past day ...
            return false;
        
        // a new day of withdrawals ...
        dateOfLatestWithdrawal = date;
        amountForLatestWithdrawalDay = 0;
        return true;
    }

    /**
     * Request a printed account statement and store the transaction for the
     * date <code>date</code>. This request may fail, in this case nothing
     * happens (the customer does not receive anything). For this reason the
     * method does not have any preconditions
     * 
     * TODO: here a nice specification seems possible ...
     */
    void requestStatement (int date) {
        final int now = Clock.getCurrentDate();
    
        addTransaction ( new AccountStatementRequest ( date ) );
        
        if ( Clock.isSameMonth ( dateOfLatestAccountStatement, now ) ) {
            if ( !newWithdrawalIsPossible(1) )
                // then this request is ignored
                return;                
            withdraw ( 1 );
        }
    
        sendAccountStatement ();
        dateOfLatestAccountStatement = now;
    }
    
    /**
     * @return the amount of money that has been withdrawn so far on the day
     *         <code>Clock.getCurrentDate()</code>
     * 
     * TODO: here a nice specification seems possible ...
     */
    private /*@ pure @*/ int getWithdrawnAmountForToday () {
        if ( Clock.isSameDay ( Clock.getCurrentDate(), dateOfLatestWithdrawal ) )
            return amountForLatestWithdrawalDay;
        return 0;
    }

    /**
     * Simulate the sending of an account statement ...
     */
    public void sendAccountStatement () {
        // do something
        System.out.println ( "Send account statement!" );
    }

    
    ////////////////////////////////////////////////////////////////////////////
    // Methods for testing
    ////////////////////////////////////////////////////////////////////////////
    
    public String toString () {
        return
            "(Account: " + getAccountNumber () +
            ", Balance: " + accountBalance () +
            ", Recent withdrawals: (" + dateOfLatestWithdrawal + ", " + amountForLatestWithdrawalDay + ")" + 
            ", Transactions: (" + transactionListToString() + "))";
    }
    
    void depose (int amount) {
        balance += amount;
    }
}
