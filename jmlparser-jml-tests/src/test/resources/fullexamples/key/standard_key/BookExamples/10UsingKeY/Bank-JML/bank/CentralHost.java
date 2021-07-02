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
 * Class that represents the central host of our bank. This class manages the
 * persistent information about accounts and is responsible for creating new
 * accounts and issuing bank cards
 */
public class CentralHost {
    
    static final int maxAccountNumber = 10000;
    
    /**
     * All accounts existing for this bank. For simplicity, here just an array
     * is used to implement a map from account number the
     * <code>PermanentAccount</code> objects. In practice this should rather
     * be a hashmap or something similar
     */
    /*@
        public invariant accounts != null;
        public invariant accounts.length == maxAccountNumber;
        public invariant (\forall int i; i >= 0 && i < maxAccountNumber;
                                         ( accounts[i] == null
                                           ||
                                           accounts[i].accountNumber == i ));
      @*/
    private /*@ spec_public, nullable @*/ final PermanentAccount[] accounts =
        new PermanentAccount [maxAccountNumber];
    
        
    /**
     * Obtain the account with number <code>accountNumber</code>
     * 
     * @param accountNumber
     *            the number of the account that is requested
     * @return the account with number <code>accountNumber</code>, or
     *         <code>null</code> iff no such account exists
     */
    /*@
        public normal_behavior
        requires  accountNumber >= 0;
        requires  accountNumber < maxAccountNumber;
        ensures   accounts[accountNumber] != null
                  ==>
                  \result.accountNumber == accountNumber;
      @*/
    public /*@ pure @*/ PermanentAccount getAccount (int accountNumber) {
        return accounts[accountNumber];
    }

    /** 
     * Retrieves the accountnumber with the maximal balance.
     * @return the accountnumber with maximal balance or <code>-1</code> if no accounts exists
     */
    /*@
        public normal_behavior
        requires (\exists int i; i>=0 && i<maxAccountNumber; accounts[i] != null);
        ensures \result != -1 && (\forall int i; i>=0 && i<maxAccountNumber; 
	      accounts[i]!=null ==> accounts[i].balance <= accounts[\result].balance);
	also
        public normal_behavior
        requires (\forall int i; i>=0 && i<maxAccountNumber; accounts[i] == null);
        ensures \result == -1;
      @*/
    public /*@ pure @*/ int getAccountWithMaxBalance() {

	int account = -1;	
	/*@ loop_invariant 
	  @    0<=i && i <= maxAccountNumber && 
	  @    account >=-1 && account < maxAccountNumber &&
	  @    (account != -1 ==> (accounts[account] != null && 
	  @     (\forall int j; (j>=0 && j<i && accounts[j] != null); 
	  @             accounts[j].balance <= accounts[account].balance))) &&
	  @    (account == -1 ==> (\forall int j; j>=0 && j<i; accounts[j] == null));
	  @ assignable i,account;
	  @ decreases maxAccountNumber - i; 
	  @*/
	 for (int i = 0; i<maxAccountNumber; i++) {	    
	    if (accountExists(i)) {
		if (account == -1) {
		    account = i;
		} else if (getAccount(i).accountBalance() > getAccount(account).accountBalance()) {
		    account = i;		
		}
	    }	    
	}

	return account;
    }


    
    /**
     * @return <code>true</code> iff there is an account with number
     *         <code>accountNumber</code>
     */
    /*@
        public normal_behavior
        requires  accountNumber >= 0;
        requires  accountNumber < maxAccountNumber;
        ensures   \result <==> accounts[accountNumber] != null;
      @*/
    public /*@ pure @*/ boolean accountExists (int accountNumber) {
        return getAccount ( accountNumber ) != null;
    }
    
    
    /**
     * Create a new account with account number <code>accountNumber</code>
     * 
     * @param accountNumber
     *            the number of the account to be created
     */
    /*@
        public normal_behavior
        requires  accountNumber >= 0;
        requires  accountNumber < maxAccountNumber;
        requires  accounts[accountNumber] == null;
        ensures   accounts[accountNumber] != null;
        assignable  accounts[accountNumber];
      @*/
    public void createAccount (int accountNumber) {
        accounts[accountNumber] = new PermanentAccount ( accountNumber, 0 );
    }
    
    
    /**
     * Issue a bank card for the account with number <code>accountNumber</code>
     * and setup the card with the given PIN
     * 
     * @param accountNumber
     *            number of the account for which a card is supposed to be
     *            issued
     * @param pin
     *            the PIN of the card to be issued
     * @return the software bank card representation
     */
    /*@
        public normal_behavior
        requires  accountNumber >= 0;
        requires  accountNumber < maxAccountNumber;
        requires  accounts[accountNumber] != null;
        ensures   \result.accountNumber == accountNumber;
        ensures   \result.correctPIN == pin;
        ensures   !\result.invalid;
        assignable \nothing;
      @*/
    public BankCard issueCard (int accountNumber, int pin) {
        return new BankCard ( accountNumber, pin );
    }
    
    
    /**
     * An example scenario
     */
    public static void main (String[] args) {
        final CentralHost ch = new CentralHost ();
        final ATM atm0 = new ATM ( ch );
        final ATM atm1 = new ATM ( ch );

        ch.createAccount ( 5 );                               Clock.tick();
        ch.createAccount ( 6 );                               Clock.tick();

        final BankCard c5 = ch.issueCard ( 5, 1234 );         Clock.tick();
        final BankCard c6 = ch.issueCard ( 6, 4321 );         Clock.tick();
        
        ch.getAccount ( 5 ).depose ( 5000 );                  Clock.tick();
        ch.getAccount ( 6 ).depose ( 300 );                   Clock.tick();

        atm1.setOnline ( false );                             Clock.tick();

        atm1.insertCard ( c5 );
        atm1.enterPIN ( 1235 );
        atm1.enterPIN ( 1234 );
        
        atm1.withdraw ( 75 );                                 Clock.tick();

        atm1.ejectCard ();
        
        System.out.println ( ch );
        
        atm0.setOnline ( false );                             Clock.tick();

        atm0.insertCard ( c5 );
        atm0.enterPIN ( 1234 );
        
        atm1.insertCard ( c6 );
        atm1.enterPIN ( 4321 );
        
        atm0.withdraw ( 75 );                                 Clock.tick();
        atm0.requestAccountStatement();                       Clock.tick();
        atm1.requestAccountStatement();                       Clock.tick();
        atm1.withdraw ( 150 );                                Clock.tick();
        atm0.withdraw ( 100 );                                Clock.tick();
        atm1.requestAccountStatement();                       Clock.tick();
        atm0.withdraw ( 950 );                                Clock.tick();

        System.out.println ( ch );

        atm0.setOnline ( true );                              Clock.tick();

        atm0.ejectCard();
        atm1.ejectCard();

        atm1.setOnline ( true );                              Clock.tick();


        System.out.println ( ch );

        Clock.tick();Clock.tick();Clock.tick();Clock.tick();Clock.tick();
        Clock.tick();Clock.tick();Clock.tick();
        
        atm0.insertCard ( c5 );
        atm0.enterPIN ( 1234 );

        atm0.withdraw ( 950 );                                Clock.tick();
        atm0.withdraw ( 950 );                                Clock.tick();
        atm0.requestAccountStatement();                       Clock.tick();

        atm0.ejectCard ();
        
        System.out.println ( ch );

        atm1.setOnline ( true );                              Clock.tick();

        System.out.println ( ch );
    }
    
    
    public String toString () {
        final StringBuffer res = new StringBuffer ();
        res.append ( "Central Host:\n" );
        for ( int i = 0; i != maxAccountNumber; ++i ) {
            if ( !accountExists ( i ) ) continue;
            res.append ( getAccount ( i ).toString () );
            res.append ( '\n' );
        }
        return res.toString ();
    }
}
