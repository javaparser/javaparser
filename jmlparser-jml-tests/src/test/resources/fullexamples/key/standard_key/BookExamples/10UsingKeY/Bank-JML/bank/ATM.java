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
 * Class whose objects represent the automated teller machines of our bank.
 * These machines can operate both online and offline. In the first case, all
 * transactions are directly transfered to the central host of the bank, in the
 * latter case transactions are first buffered (using class
 * <code>OfflineAccountProxy</code> and later written back to the central
 * host.
 */
public class ATM {
    
    static final int maxAccountNumber = CentralHost.maxAccountNumber;    

    /**
     * Currently instantiated offline account representatives. For simplicity,
     * here just an array is used to implement a map from account number the
     * <code>OfflineAccountProxy</code> objects. In practice this should
     * rather be a hashmap or something similar
     */
    /*@
        public invariant accountProxies != null;
        public invariant accountProxies.length == maxAccountNumber;
        public invariant (\forall int i; i >= 0 && i < maxAccountNumber;
                                         ( accountProxies[i] == null
                                           ||
                                           accountProxies[i].accountNumber == i ));
	public invariant (\forall ATM a; a != self; a.insertedCard == null || a.insertedCard != self.insertedCard);
      @*/
    private /*@ spec_public, nullable @*/ final OfflineAccountProxy[] accountProxies =
        new OfflineAccountProxy [maxAccountNumber];

    /**
     * The central host of the bank. We suppose that the attribute is only
     * accessed if the ATM is online to abstract from the actual communication 
     */
    private /*@ spec_public @*/ final CentralHost centralHost;
    
    /**
     * <code>true</code> iff the ATM is online, i.e. if
     * <code>centralHost</code> may be accessed
     */
    private /*@ spec_public @*/ boolean  online = true;
    
    /**
     * A bank card that is possible inserted into the ATM at the time
     */
    private /*@ spec_public, nullable @*/ BankCard insertedCard          = null;
    /**
     * <code>true</code> iff there is a card inserted and the customer has
     * entered the right PIN
     */
    private /*@ spec_public @*/ boolean  customerAuthenticated = false;
    /**
     * Count the number of wrong PINs entered since a valid card was inserted
     */
    private /*@ spec_public @*/ int      wrongPINCounter       = 0;
    
    /*@
        private invariant customerAuthenticated ==> insertedCard != null;
        private invariant insertedCard != null ==> !insertedCard.invalid;
        private invariant insertedCard != null ==>
                                 insertedCard.accountNumber >= 0;
        private invariant insertedCard != null ==>
                                 insertedCard.accountNumber < maxAccountNumber;
        private invariant ( online && insertedCard != null )
                          ==>
                          centralHost.accounts[insertedCard.accountNumber] != null;
      @*/
    
    /*@
        public normal_behavior
        requires  centralHost != null;
      @*/
    public /*@ pure @*/ ATM (final CentralHost centralHost) {
        this.centralHost = centralHost;
    }

    
    /**
     * @return <code>true</code> iff the ATM is online
     */
    private /*@ pure @*/ boolean isOnline () {
        return online;
    }
    
    
    /**
     * Access the account with number <code>accountNumber</code>. This either
     * returns the permanent account objects that is stored by the central host,
     * or an offline proxy
     * 
     * @param accountNumber
     *            the number of the account to be accessed
     * @return a representation of the account
     * 
     * TODO: The precondition can in practice not be ensured by the ATM (if it
     * is offline)
     */
    /*@
        private normal_behavior
        requires  accountNumber >= 0;
        requires  accountNumber < maxAccountNumber;
        requires  centralHost.accounts[accountNumber] != null;
        ensures   \result.accountNumber == accountNumber;
        assignable accountProxies[accountNumber],\object_creation(bank.OfflineAccountProxy);
      @*/
    private Account getAccount (int accountNumber) {
        if ( isOnline () ) return centralHost.getAccount ( accountNumber );

        if ( !proxyExists ( accountNumber ) )
            setProxy ( accountNumber, new OfflineAccountProxy ( accountNumber ) );

        return getProxy ( accountNumber );
    }


    /**
     * Switch the status of <code>this</code> ATM to online or offline.
     * Switching to online will make the terminal write back all buffered
     * transactions to the central host and remove all account proxies.
     * 
     * TODO: one of the places where both complete specification and
     * verification are non-trivial
     * 
     * @param newOnline
     *            <code>true</code> iff the terminal is switched online
     */
    /*@
        public normal_behavior
        ensures  online == newOnline;
        assignable \everything;
      @*/
    public void setOnline (boolean newOnline) {
        if ( this.online == newOnline ) return;
        
        if ( newOnline ) {
            System.out.println("ATM turned online ...");
            
            // synchronize with central host
            for ( int i = 0; i != CentralHost.maxAccountNumber; ++i ) {
                if ( proxyExists ( i ) ) {
                    getProxy ( i ).replay ( centralHost.getAccount ( i ) );
                    setProxy ( i, null );
                }
            }
        } else {
            System.out.println("ATM turned offline ...");            
        }
        
        if ( cardForNonexistingAccountInserted () ) confiscateCard ();
        
        this.online = newOnline;
    }
    
    
    ////////////////////////////////////////////////////////////////////////////
    // Methods for authentication of customers: Insertion of bank cards,
    // entering of PINs, etc.
    //
    // The public methods are written more defensively and throw a <code>
    // RuntimeException </code> in case of violated preconditions
    ////////////////////////////////////////////////////////////////////////////
    
    /**
     * Insert the given card into the ATM. This will check whether the card is
     * invalid or the card belongs to a non-existing account (if the terminal is
     * online); in this case the card is directly confiscated
     * 
     * @param card
     *            the card to be inserted
     */
    /*@
        public normal_behavior
        requires  insertedCard == null;
        requires  card != null;
        requires  card.accountNumber >= 0;
        requires  card.accountNumber < maxAccountNumber;
	requires  (\forall ATM a; a.insertedCard != card);
        ensures   card.invalid <==> insertedCard == null;
        ensures   !customerAuthenticated;
        ensures   wrongPINCounter == 0;
        assignable insertedCard, customerAuthenticated, wrongPINCounter, card.invalid;
      @*/
    public void insertCard (BankCard card) {
        if ( !( !cardIsInserted () && card != null
                && card.getAccountNumber () >= 0
                && card.getAccountNumber () < maxAccountNumber ) )
                                throw new RuntimeException ();
        
        insertedCard = card;
        customerAuthenticated = false;
        wrongPINCounter = 0;
        if ( insertedCard.cardIsInvalid ()
             || cardForNonexistingAccountInserted () )
            confiscateCard ();
    }
    
    
    /**
     * Eject an inserted card
     * 
     * @return the card that was inserted previously
     */
    /*@
        public normal_behavior
        requires  insertedCard != null;
        ensures   insertedCard == null;
        assignable insertedCard, customerAuthenticated;
      @*/
    public BankCard ejectCard () {
        if ( !cardIsInserted() ) throw new RuntimeException ();

        final BankCard res = insertedCard;
        
        insertedCard = null;
        customerAuthenticated = false;
        
        return res;
    }
    
    
    /**
     * Confiscate an inserted card. This invalidates the card; afterwards, the
     * card is no longer regarded as inserted
     */
    /*@
        public normal_behavior
        requires  insertedCard != null;
        ensures   insertedCard == null;
        ensures   \old(insertedCard).invalid;
        assignable insertedCard, customerAuthenticated, insertedCard.invalid;
      @*/
    public void confiscateCard () {
        if ( !cardIsInserted() ) throw new RuntimeException ();

        insertedCard.makeCardInvalid ();
        insertedCard = null;
        customerAuthenticated = false;        
    }
    
    
    /**
     * Enter the PIN the belongs to the currently inserted bank card into the
     * ATM. If a wrong PIN is entered three times in a row, the card is
     * confiscated. After having entered the correct PIN, the customer is
     * regarded is authenticated
     * 
     * @param pin
     *            the PIN that is entered
     */
    /*@ public normal_behavior
        requires  insertedCard != null;
        requires  !customerAuthenticated;
        requires  pin == insertedCard.correctPIN;
        assignable customerAuthenticated;      
        ensures   customerAuthenticated;
      
        also
      
        public normal_behavior
        requires  insertedCard != null;
        requires  !customerAuthenticated;
        requires  pin != insertedCard.correctPIN;
        requires  wrongPINCounter < 2;
        assignable wrongPINCounter;
        ensures   wrongPINCounter 
                        == \old(wrongPINCounter) + 1;
        ensures   !customerAuthenticated;
      
        also
        
        public normal_behavior
        requires  insertedCard != null;
        requires  !customerAuthenticated;
        requires  pin != insertedCard.correctPIN;
        requires  wrongPINCounter >= 2;
        assignable insertedCard, wrongPINCounter, 
                   insertedCard.invalid;    
        ensures   insertedCard == null;
        ensures   \old(insertedCard).invalid;
        ensures   !customerAuthenticated;
      @*/
    public void enterPIN (int pin) {
        if ( !( cardIsInserted () && !customerIsAuthenticated () ) )
                                    throw new RuntimeException ();

        if ( insertedCard.pinIsCorrect ( pin ) ) {
            customerAuthenticated = true;
        } else {
            ++wrongPINCounter;
            if ( wrongPINCounter >= 3 ) confiscateCard ();
        }
    }
    
    
    /**
     * @return <code>true</code> iff a card is inserted in the ATM
     */
    private /*@ pure @*/ boolean cardIsInserted () {
        return insertedCard != null;
    }
    
    
    /**
     * @return <code>true</code> iff a customer is regarded as authenticated,
     *         i.e. if a valid card is inserted and the correct PIN has be
     *         entered
     */
    private /*@ pure @*/ boolean customerIsAuthenticated () {
        return customerAuthenticated;
    }

    
    /**
     * Check whether the currently inserted card belongs to an account that does
     * actually not exist
     * 
     * TODO: great postcondition ...
     * 
     * @return <code>true</code> iff there is a card inserted, the ATM is
     *         online and the card belongs to a non-existing account
     */
    /*@
        private normal_behavior
        ensures  \result
                 <==>
                 ( insertedCard != null
                   &&
                   online
                   &&
                   centralHost.accounts[insertedCard.accountNumber] == null );
      @*/
    private /*@ pure @*/ boolean cardForNonexistingAccountInserted () {
        return
            cardIsInserted ()
            && isOnline ()
            && !centralHost.accountExists ( getAccountNumber () );
    }
    
    
    
    ////////////////////////////////////////////////////////////////////////////
    // Methods for accessing an account after successful authentication
    //
    // The public methods are written more defensively and throw a <code>
    // RuntimeException </code> in case of violated preconditions
    ////////////////////////////////////////////////////////////////////////////
    
    /**
     * @return the account number of the account that belongs to the currently
     *         inserted card
     */
    /*@
        private normal_behavior
        requires  customerAuthenticated;
      @*/
    private /*@ pure @*/ int getAccountNumber () {
        return insertedCard.getAccountNumber ();
    }

    /**
     * @return the account that belongs to the currently inserted card
     */
    /*@
        private normal_behavior
        requires  customerAuthenticated;
        assignable accountProxies[insertedCard.accountNumber],\object_creation(bank.OfflineAccountProxy);
      @*/
    private Account getAccount () {
        return getAccount ( getAccountNumber () );
    }

    
    /**
     * Determine the balance of the current account.
     * 
     * @return the balance of the current account, provided that the balance is
     *         available (only in the online case). Otherwise <code>0</code>
     *         is returned
     * 
     * TODO: make online a precondition?
     */
    /*@
        public normal_behavior
        requires  customerAuthenticated;
        ensures   online
                  ==>
                  \result ==
                     centralHost.accounts[insertedCard.accountNumber].balance;
        assignable accountProxies[insertedCard.accountNumber],\object_creation(bank.OfflineAccountProxy);
      @*/
    public int accountBalance () {
        if ( !customerIsAuthenticated () ) throw new RuntimeException ();
        if ( !getAccount ().balanceIsAccessible () ) return 0;
        return getAccount ().accountBalance ();
    }
    
    
    /**
     * Try to withdraw <code>amount</code> from the current account.
     * 
     * TODO: make specification stronger, say something about the return value?
     * 
     * @param amount
     *            the amount that is supposed to be withdrawn
     * 
     * @return the amount of money that was sucessfully withdrawn (i.e. in case
     *         of failure the return value is <code>0</code>)
     */
    /*@
        public normal_behavior
        requires  customerAuthenticated;
        requires  amount > 0;
	assignable \object_creation(bank.OfflineAccountProxy),\object_creation(java.lang.RuntimeException);
      @*/
    public int withdraw (int amount) {
        if ( !( customerIsAuthenticated () && amount > 0 ) )
                                    throw new RuntimeException ();
        return getAccount ().checkAndWithdraw ( amount );
    }

    
    /**
     * Request a printed account statement for the current account
     */
    /*@
        public normal_behavior
        requires  customerAuthenticated;
	assignable \object_creation(bank.OfflineAccountProxy),\object_creation(java.lang.RuntimeException);
      @*/
    public void requestAccountStatement () {
        if ( !customerIsAuthenticated () ) throw new RuntimeException ();
        getAccount ().requestStatement ();
    }

    
    
    ////////////////////////////////////////////////////////////////////////////
    // Internal methods for controlling account proxies
    ////////////////////////////////////////////////////////////////////////////
    
    /**
     * Update the mapping of account numbers to account proxies
     */
    /*@
        private normal_behavior
        requires  accountNumber >= 0;
        requires  accountNumber < maxAccountNumber;
        ensures   accountProxies[accountNumber] == proxy;
        assignable accountProxies[accountNumber];
      @*/
    private void setProxy (int accountNumber, OfflineAccountProxy proxy) {
        accountProxies[accountNumber] = proxy;
    }

    /**
     * Map an account number to a possibly stored account proxy
     * 
     * @return the account proxy for account number <code>accountNumber</code>,
     *         or <code>null</code> if no such proxy exists
     */
    /*@
        private normal_behavior
        requires  accountNumber >= 0;
        requires  accountNumber < maxAccountNumber;
        ensures   \result == accountProxies[accountNumber];
      @*/
    private /*@ pure @*/ OfflineAccountProxy getProxy (int accountNumber) {
        return accountProxies[accountNumber];
    }

    /**
     * @return <code>true</code> if there is a proxy for account number
     *         <code>accountNumber</code> stored in this object
     */
    /*@
        private normal_behavior
        requires  accountNumber >= 0;
        requires  accountNumber < maxAccountNumber;
        ensures   \result <==> accountProxies[accountNumber] != null;
      @*/
    private /*@ pure @*/ boolean proxyExists (int accountNumber) {
        return getProxy ( accountNumber ) != null;
    }
}
