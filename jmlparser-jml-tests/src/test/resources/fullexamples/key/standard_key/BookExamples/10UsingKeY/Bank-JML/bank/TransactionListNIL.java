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
 * Singleton class for empty lists of transactions
 * @stereotype singleton
 */
public /*@ pure @*/ class TransactionListNIL extends TransactionList {
    
    /**
     * This class is a singleton, to access the only object use
     * <code>TransactionList.EMPTY_LIST</code>
     */
    protected TransactionListNIL() {}
    
    /**
     * @return the first element of <code>this</code> list, or
     *         <code>null</code> iff this list is empty
     * 
     * @stereotype query
     */
    public Transaction head () {
        return null;
    }

    /**
     * @return the tail (the list without its first element) of
     *         <code>this</code> list, or <code>null</code> iff this list is
     *         empty
     * 
     * @stereotype query
     */
    public TransactionList tail () {
        return null;
    }

    /**
     * @return <code>true</code> iff <code>this</code> list is empty
     * 
     * @stereotype query
     */
    public boolean isEmpty () {
        return true;
    }

    /**
     * @return the length of this list
     * 
     * @stereotype query
     */
    public int length () {
        return 0;
    }
}
