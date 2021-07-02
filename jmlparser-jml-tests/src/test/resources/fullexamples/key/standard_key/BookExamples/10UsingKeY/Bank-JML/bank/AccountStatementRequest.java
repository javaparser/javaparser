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
 * Class for representing the transaction of requesting a printed account
 * statement.
 * Objects of this class are immutable
 */
public class AccountStatementRequest extends Transaction {

    public /*@ pure @*/ AccountStatementRequest (int date) {
        super ( date );
    }

    /**
     * The design pattern "Strategy" is used for implementing the
     * synchronisation of offline account proxies with the permanent accounts.
     * Invoking this method carries out <code>this</code> transaction an the
     * real account. Note that the statement is requested for the correct date,
     * though this is meaningless because of the implementation of
     * <code>PermanentAccount.requestStatement</code>
     * 
     * @param target
     *            the permanent account on which <code>this</code> transaction
     *            is supposed to be carried out
     */
    public void replay (PermanentAccount target) {
        target.requestStatement ( getDate () );
    }

    public /*@ pure @*/ String toString () {
        return "" + getDate() + ":AccountStatement";
    }
}
