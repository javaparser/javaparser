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
 * Class for representing non-empty lists of transactions. 
 */
public /*@ pure @*/ class TransactionListCons extends TransactionList {
    
    /**
     * The first element of the list
     */
    private final Transaction data;
    
    /**
     * The tail of the list
     */
    private final TransactionList next;
    
    /**
     * The length of the list
     */
    private final int len;

    /**
     * Use the method <code>TransactionList.prepend</code> for creating
     * non-empty lists
     */
    protected TransactionListCons (final Transaction data,
                                   final TransactionList next) {
        this.data = data;
        this.next = next;
        this.len = next.length () + 1;
    }
    
    /**
     * @return the first element of <code>this</code> list, or
     *         <code>null</code> iff this list is empty
     */
    public Transaction head () {
        return data;
    }
    
    /**
     * @return the tail (the list without its first element) of
     *         <code>this</code> list, or <code>null</code> iff this list is
     *         empty
     */
    public TransactionList tail() {
        return next;
    }
    
    /**
     * @return <code>true</code> iff <code>this</code> list is empty
     */
    public boolean isEmpty () {
        return false;
    }
    
    /**
     * @return the length of this list
     */
    public int length () {
        return len;
    }
}
