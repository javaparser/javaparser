// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package javacard.framework;

public final class JCSystem {

    private static native void nativeKeYBeginTransaction();
    private static native void nativeKeYAbortTransaction();
    private static native void nativeKeYCommitTransaction();

    static native byte nativeKeYGetTransient(Object o);
    static native void nativeKeYSetTransient(Object o, byte transientType);

    public static final byte NOT_A_TRANSIENT_OBJECT = (byte) 0;
    //@ public invariant NOT_A_TRANSIENT_OBJECT == 0;
    public static final byte CLEAR_ON_RESET = (byte) 1;
    //@ public invariant CLEAR_ON_RESET == 1;
    public static final byte CLEAR_ON_DESELECT = (byte) 2;
    //@ public invariant CLEAR_ON_DESELECT == 2;

    public static final byte MEMORY_TYPE_PERSISTENT = (byte) 0;
    //@ public invariant MEMORY_TYPE_PERSISTENT == 0;
    public static final byte MEMORY_TYPE_TRANSIENT_RESET = (byte) 1;
    //@ public invariant MEMORY_TYPE_TRANSIENT_RESET == 1;
    public static final byte MEMORY_TYPE_TRANSIENT_DESELECT = (byte) 2;
    //@ public invariant MEMORY_TYPE_TRANSIENT_DESELECT == 2;

    private /*@ spec_public @*/ static final short API_VERSION = (short) 0x0202;
    //@ public invariant API_VERSION == 0x0202;

    /*@ public normal_behavior
          ensures o == null ==> \result == JCSystem.NOT_A_TRANSIENT_OBJECT;
          ensures o != null ==> \result == o.\transient;
          accessible o.\transient;
          assignable<heap> \strictly_nothing;
          assignable<savedHeap> \strictly_nothing;
      @*/
    public static byte isTransient(Object o) {
       if(o == null) { return 0; }
       return nativeKeYGetTransient(o);
    }

    private static /*@ spec_public @*/ byte _transactionDepth = (byte)0;
    //@ public invariant getTransactionDepth() == 0 || getTransactionDepth() == 1;

    /*@ public normal_behavior
          ensures \result == _transactionDepth;
          accessible JCSystem._transactionDepth;
          assignable<heap> \strictly_nothing;
          assignable<savedHeap> \strictly_nothing;
          @*/
    public static byte getTransactionDepth() {
      return _transactionDepth;
    }

    /*@ spec_public nullable @*/ static NegativeArraySizeException nase = new NegativeArraySizeException();
    //@ public invariant nase != null;

    /*@ spec_public nullable @*/ static NullPointerException npe = new NullPointerException();
    //@ public invariant npe != null;

    /*@ spec_public nullable @*/ static ArrayIndexOutOfBoundsException aioobe = new ArrayIndexOutOfBoundsException();
    //@ public invariant aioobe != null;

    /*@ public normal_behavior
          requires length >= 0;
          requires event == JCSystem.CLEAR_ON_RESET || event == JCSystem.CLEAR_ON_DESELECT;
          ensures \fresh(\result);
          ensures \result.length == length;
          ensures JCSystem.isTransient(\result) == event;
          ensures !\transactionUpdated(\result);
          ensures \typeof(\result) == \type(boolean[]);
          ensures (\forall int i; i>=0 && i<\result.length; !\result[i]);
          assignable \nothing;
      @*/
    public static /*@ non_null @*/ boolean[] makeTransientBooleanArray(short length, byte event)
            throws SystemException, NegativeArraySizeException {
        if (event != CLEAR_ON_RESET && event != CLEAR_ON_DESELECT) {
            SystemException.throwIt(SystemException.ILLEGAL_VALUE);
        }
        /*
        if (!KeYJCSystem.systemInitializationInProgress && event == CLEAR_ON_DESELECT
                && KeYJCSystem
                        .jvmGetContext(KeYJCSystem.selectedApplets[KeYJCSystem.currentChannel]) != KeYJCSystem
                        .jvmGetContext(KeYJCSystem
                                .jvmGetOwner(KeYJCSystem.currentActiveObject)))
            SystemException.throwIt(SystemException.ILLEGAL_TRANSIENT);
        */
        if (length < 0) {
            throw nase;
        }
        boolean[] result = new boolean[length];
        nativeKeYSetTransient(result, event);
        // KeYHelper.setJavaOwner(result, null);
        return result;
    }

    /*@ public normal_behavior
          requires length >= 0;
          requires event == JCSystem.CLEAR_ON_RESET || event == JCSystem.CLEAR_ON_DESELECT;
          ensures \fresh(\result);
          ensures \result.length == length;
          ensures JCSystem.isTransient(\result) == event;
          ensures !\transactionUpdated(\result);
          ensures \typeof(\result) == \type(byte[]);
          ensures (\forall int i; i>=0 && i<\result.length; \result[i] == 0);
          assignable \nothing;
      @*/
    public static /*@ non_null @*/ byte[] makeTransientByteArray(short length, byte event)
            throws SystemException, NegativeArraySizeException {
        if (event != CLEAR_ON_RESET && event != CLEAR_ON_DESELECT) {
            SystemException.throwIt(SystemException.ILLEGAL_VALUE);
        }
        /*
        if (!KeYJCSystem.systemInitializationInProgress && event == CLEAR_ON_DESELECT
                && KeYJCSystem
                        .jvmGetContext(KeYJCSystem.selectedApplets[KeYJCSystem.currentChannel]) != KeYJCSystem
                        .jvmGetContext(KeYJCSystem
                                .jvmGetOwner(KeYJCSystem.currentActiveObject)))
            SystemException.throwIt(SystemException.ILLEGAL_TRANSIENT);
        */
        if (length < 0) {
            throw nase;
        }
        byte[] result = new byte[length];
        nativeKeYSetTransient(result, event);
        // KeYHelper.setJavaOwner(result, null);
        return result;
    }

    /*@ public normal_behavior
          requires length >= 0;
          requires event == JCSystem.CLEAR_ON_RESET || event == JCSystem.CLEAR_ON_DESELECT;
          ensures \fresh(\result);
          ensures \result.length == length;
          ensures JCSystem.isTransient(\result) == event;
          ensures !\transactionUpdated(\result);
          ensures \typeof(\result) == \type(short[]);
          ensures (\forall int i; i>=0 && i<\result.length; \result[i] == 0);
          assignable \nothing;
      @*/
    public static /*@ non_null @*/ short[] makeTransientShortArray(short length, byte event)
            throws SystemException, NegativeArraySizeException {
        if (event != CLEAR_ON_RESET && event != CLEAR_ON_DESELECT) {
            SystemException.throwIt(SystemException.ILLEGAL_VALUE);
        }
        /*
        if (!KeYJCSystem.systemInitializationInProgress && event == CLEAR_ON_DESELECT
                && KeYJCSystem
                        .jvmGetContext(KeYJCSystem.selectedApplets[KeYJCSystem.currentChannel]) != KeYJCSystem
                        .jvmGetContext(KeYJCSystem
                                .jvmGetOwner(KeYJCSystem.currentActiveObject)))
            SystemException.throwIt(SystemException.ILLEGAL_TRANSIENT);
        */
        if (length < 0) {
            throw nase;
        }
        short[] result = new short[length];
        nativeKeYSetTransient(result, event);
        // KeYHelper.setJavaOwner(result, null);
        return result;
    }

    /*@ public normal_behavior
          requires length >= 0;
          requires event == JCSystem.CLEAR_ON_RESET || event == JCSystem.CLEAR_ON_DESELECT;
          ensures \fresh(\result);
          ensures \result != null;
          ensures \result.length == length;
          ensures JCSystem.isTransient(\result) == event;
          ensures !\transactionUpdated(\result);
          ensures \typeof(\result) == \type(Object[]);
          ensures (\forall int i; i>=0 && i<\result.length; \result[i] == null);
          assignable \nothing;
      @*/
    public static /*@ nullable @*/ java.lang.Object[] makeTransientObjectArray(short length, byte event)
            throws SystemException, NegativeArraySizeException {
        if (event != CLEAR_ON_RESET && event != CLEAR_ON_DESELECT) {
            SystemException.throwIt(SystemException.ILLEGAL_VALUE);
        }
        /*
        if (!KeYJCSystem.systemInitializationInProgress && event == CLEAR_ON_DESELECT
                && KeYJCSystem
                        .jvmGetContext(KeYJCSystem.selectedApplets[KeYJCSystem.currentChannel]) != KeYJCSystem
                        .jvmGetContext(KeYJCSystem
                                .jvmGetOwner(KeYJCSystem.currentActiveObject)))
            SystemException.throwIt(SystemException.ILLEGAL_TRANSIENT);
        */
        if (length < 0) {
            throw nase;
        }
        java.lang.Object[] result = new java.lang.Object[length];
        nativeKeYSetTransient(result, event);
        // KeYHelper.setJavaOwner(result, null);
        return result;
    }

    // no spec
    public static void beginTransaction() throws TransactionException {
        if (_transactionDepth != 0)
            TransactionException.throwIt(TransactionException.IN_PROGRESS);
        _transactionDepth++;
        nativeKeYBeginTransaction();
    }

    // no spec
    public static void abortTransaction() throws TransactionException {
        if (_transactionDepth == 0)
            TransactionException.throwIt(TransactionException.NOT_IN_PROGRESS);
        nativeKeYAbortTransaction();
        _transactionDepth--;
    }

    // no spec
    public static void commitTransaction() throws TransactionException {
        if (_transactionDepth == 0)
            TransactionException.throwIt(TransactionException.NOT_IN_PROGRESS);
        nativeKeYCommitTransaction();
        _transactionDepth--;
    }

}
