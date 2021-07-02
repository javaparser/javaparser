package ATM_Example_JML; 

/**
 * Class whose objects represent the automated teller machines of a bank.
 */
public /*@ nullable_by_default @*/ class ATM {
    
    static final int maxAccountNumber = CentralHost.maxAccountNumber;    

   /**
     * The central host of the bank. We suppose that the attribute is only
     * accessed if the ATM is online to abstract from the actual communication 
     */
    //@ private invariant centralHost != null;
    private /*@ spec_public @*/ final CentralHost centralHost;
    
    /**
     * <code>true</code> iff the ATM is online, i.e. if
     * <code>centralHost</code> may be accessed
     */
    private /*@ spec_public @*/ boolean  online = true;
    
    /**
     * A bank card that is possible inserted into the ATM at the time
     */
    private /*@ spec_public @*/ BankCard insertedCard          = null;
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
        private invariant insertedCard != null ==> \invariant_for(insertedCard);
        private invariant insertedCard != null ==>
                                 insertedCard.accountNumber >= 0;
        private invariant insertedCard != null ==>
                                 insertedCard.accountNumber < maxAccountNumber;
	private invariant (\forall ATM a; a != this; a.insertedCard == null || a.insertedCard != this.insertedCard);
        accessible \inv: customerAuthenticated, insertedCard;
      @*/
    
    /*@
        public normal_behavior
        requires centralHost != null;
      @*/
    public ATM (final CentralHost centralHost) {
        this.centralHost = centralHost;
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
        requires  \invariant_for(card);
        requires  !card.invalid;
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
        if ( insertedCard.cardIsInvalid () )
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
    /*@
        public normal_behavior
        requires  insertedCard != null;
        requires  !customerAuthenticated;
        requires  pin == insertedCard.correctPIN;
        ensures   customerAuthenticated;
        assignable customerAuthenticated;
        
        also
        
        public normal_behavior
        requires  insertedCard != null;
        requires  !customerAuthenticated;
        requires  pin != insertedCard.correctPIN;
        requires  wrongPINCounter < 2;
        ensures   wrongPINCounter == \old(wrongPINCounter) + 1;
        assignable wrongPINCounter;
        
        also
        
        public normal_behavior
        requires  insertedCard != null;
        requires  !customerAuthenticated;
        requires  pin != insertedCard.correctPIN;
        requires  wrongPINCounter >= 2;
        ensures   insertedCard == null;
        ensures   \old(insertedCard).invalid;
        assignable insertedCard, wrongPINCounter, insertedCard.invalid;
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
    private /*@ strictly_pure @*/ boolean cardIsInserted () {
        return insertedCard != null;
    }
        
    /**
     * @return <code>true</code> iff a customer is regarded as authenticated,
     *         i.e. if a valid card is inserted and the correct PIN has be
     *         entered
     */
    private /*@ strictly_pure @*/ boolean customerIsAuthenticated () {
        return customerAuthenticated;
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
	requires insertedCard != null;
        requires customerAuthenticated;
      @*/
    private /*@ strictly_pure @*/ int getAccountNumber () {
        return insertedCard.getAccountNumber ();
    }
        
}
