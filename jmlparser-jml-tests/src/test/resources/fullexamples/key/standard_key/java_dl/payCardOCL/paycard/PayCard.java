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

public class PayCard {
    int limit=1000;
    int unsuccessfulOperations;
    int id;
    int balance=0;

    public PayCard(int limit) {
        balance = 0;
        unsuccessfulOperations=0;
        this.limit=limit;
    }

    public PayCard() {
	balance=0;
        unsuccessfulOperations=0;
    }

    /* @preconditions amount>0
     * @postconditions balance>=balance@pre
     */
   public void charge(int amount) {
        if (this.balance+amount>=this.limit) {
            this.unsuccessfulOperations++;
        } else {
            this.balance=this.balance+amount;
        }
    }

    // @postconditions result=balance or unsuccessfulOperations>3
    public int available() {
	if (unsuccessfulOperations<=3) {
	    return this.balance;
        }
        return 0;
    }


    public String infoCardMsg() {
        return (" Current balance on card is " + balance);
    }
}
