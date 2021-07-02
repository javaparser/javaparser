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

package paycard;

public class PayCardJunior extends PayCard {

   /* @invariants (self.balance >= 0) 
    *             and (self.balance < juniorLimit) 
    *             and (juniorLimit<limit) 
    */

    private final static int juniorLimit=100;
    private int unsuccessfulOperations=0;

    // @preconditions cardLimit<juniorLimit 
    public PayCardJunior(int cardLimit) {
	super(cardLimit);
    }

    // @postconditions result.limit=10
    public static PayCardJunior createCard() {
		return new PayCardJunior(100);
    }

    /* @preconditions amount>0
     * @postconditions if (balance@pre+amount<juniorLimit)
     *                 then (balance=balance@pre+amount)
     *                 else ((balance=balance@pre) 
     *                       and (unsuccessfulOperations=unsuccessfulOperations@pre+1)) 
     *                 endif
     */
    public void charge(int amount) {
        try {
            this.charge0(amount);
        } catch (java.lang.Exception e) {
            this.unsuccessfulOperations++;
        }
    }

    private void charge0(int amount) throws CardException {
        int checkStatus = this.checkSum(this.balance + amount);
        if (checkStatus == 0) {
            throw new CardException();
        } else {
            this.balance = this.balance + amount;
        }
    }
    
    /* @postconditions if (result=1) then (sum<juniorLimit)
     *                               else (sum>=juniorLimit) endif
     */
    private int checkSum(int sum) {
        if (sum >= this.juniorLimit) {
            return 0;
        } else {
            return 1;
        }
    }

    /* @preconditions amount>0
     * @postconditions if (balance@pre+amount<limit)
     *                 then (amount=balance-balance@pre)
     *                 else (balance=balance@pre) 
     *                       and (unsuccessfulOperations=unsuccessfulOperations@pre+1) 
     *                 endif
     */
    public void complexCharge(int amount) {
        try {
            this.charge0(amount);
        } catch (CardException e) {
            this.unsuccessfulOperations++;
        }
    }
}
