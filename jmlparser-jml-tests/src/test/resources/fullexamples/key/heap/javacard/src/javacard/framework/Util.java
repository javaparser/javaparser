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

public class Util {

    /*@
         public behavior
           requires JCSystem.npe != null;
           requires JCSystem.aioobe != null;
           requires<savedHeap> JCSystem.isTransient(dest) != JCSystem.NOT_A_TRANSIENT_OBJECT ==> !\transactionUpdated(dest);
           ensures \result == destOffset + length;
           ensures (\forall short i; i>=0 && i<length; dest[destOffset + i] == \old(src[srcOffset + i]));
           ensures<savedHeap> (\forall short i; i>=0 && i<length; \backup(dest[destOffset + i]) == 
                 ((JCSystem.isTransient(dest) == JCSystem.NOT_A_TRANSIENT_OBJECT && \backup(\transactionUpdated(dest))) ?  
                    \old(\backup(dest[destOffset + i]))
                  : \old(src[srcOffset + i]))
              );
           signals (NullPointerException npe) npe == JCSystem.npe && (src == null || dest == null);
           signals (ArrayIndexOutOfBoundsException aioobe) aioobe == JCSystem.aioobe && (length < 0 ||
               srcOffset < 0 || destOffset < 0 ||
               srcOffset + length > src.length || destOffset + length > dest.length);
           signals_only NullPointerException, ArrayIndexOutOfBoundsException;
           assignable<heap><savedHeap> dest[destOffset..destOffset+length-1];
      @*/
    public static final short arrayCopyNonAtomic(/*@ nullable @*/ byte[] src, short srcOffset,
            /*@ nullable @*/ byte[] dest, short destOffset, short length)
            throws NullPointerException, ArrayIndexOutOfBoundsException {

        if (src == null || dest == null)
            throw JCSystem.npe;
        if (length < 0 || srcOffset < 0 || destOffset < 0
                || srcOffset  > (short)(src.length - length)
                || destOffset > (short)(dest.length - length))
            throw JCSystem.aioobe;

        if(src == dest && srcOffset == destOffset) {
          return (short) (destOffset + length);
        }
        final boolean changeTransient =
          (JCSystem.nativeKeYGetTransient(dest) == JCSystem.NOT_A_TRANSIENT_OBJECT);
        if(changeTransient) {
          JCSystem.nativeKeYSetTransient(dest, JCSystem.CLEAR_ON_RESET);
        }
        if(src != dest || srcOffset > destOffset) {
          /*@
             loop_invariant i >= 0 && i <= length &&
                srcOffset + i >= 0 && srcOffset + i <= src.length &&
                destOffset + i >= 0 && destOffset + i <= dest.length &&
               (\forall short j; j >= 0 && j< length;
                   dest[destOffset + j] == (j<i ? \old(src[srcOffset + j]) : \old(dest[destOffset + j]))
               )
             ;
             loop_invariant<savedHeap>
               (\forall short j; j >= 0 && j < length; 
                  \backup(dest[destOffset + j]) ==
                    ((j >= i || \backup(\transactionUpdated(dest))) ?
                        \old(\backup(dest[destOffset + j])) :
                        \old(src[srcOffset + j]))
               );
             decreases length - i;
             assignable<heap><savedHeap> dest[destOffset..destOffset+length-1];
          @*/
          for(short i=0;i<length;i++) {
              dest[destOffset + i] = src[srcOffset + i];
          }
        }else{
          /*@
             loop_invariant i >= 0 && i <= length &&
                srcOffset + length - i >= 0 && srcOffset + length - i  <= src.length &&
                destOffset + length - i >= 0 && destOffset + length - i <= dest.length
                &&
                (\forall short j; j >= 0 && j < length; 
                    dest[destOffset + j] == (j >= length - i ? \old(src[srcOffset + j]) : \old(dest[destOffset + j]))
                )
             ;
             loop_invariant<savedHeap>
               (\forall short j; j >= 0 && j < length; 
                  \backup(dest[destOffset + j]) ==
                    ((j < length - i || \backup(\transactionUpdated(dest))) ?
                        \old(\backup(dest[destOffset + j])) :
                        \old(src[srcOffset + j]))
               );
             decreases length - i;
             assignable dest[destOffset..destOffset+length-1];
             assignable<heap><savedHeap> dest[destOffset..destOffset+length-1];
          @*/
          for(short i=0; i<length; i++) {
            dest[destOffset + (length - 1) - i] = src[srcOffset + (length - 1) - i];
          }
        }
        if(changeTransient) {      
          JCSystem.nativeKeYSetTransient(dest, JCSystem.NOT_A_TRANSIENT_OBJECT);
        }
        return (short) (destOffset + length);
    }


    // arrayCopy is currently not provable because of bug #1284
    /*@
         public behavior
           requires JCSystem.npe != null;
           requires JCSystem.aioobe != null;
//           requires javacard.framework.JCSystem.getTransactionDepth() == 0;
//           requires<savedHeap> javacard.framework.JCSystem.getTransactionDepth() == 1;
           requires JCSystem.isTransient(dest) != JCSystem.NOT_A_TRANSIENT_OBJECT ==> !\transactionUpdated(dest);
           ensures \result == destOffset + length;
           ensures (\forall short i; i>=0 && i<length; dest[destOffset + i] == \old(src[srcOffset + i]));
           ensures<savedHeap> (JCSystem.isTransient(dest) == JCSystem.NOT_A_TRANSIENT_OBJECT && length > 0 && (src != dest || srcOffset != destOffset))
                ==> \backup(\transactionUpdated(dest));
           ensures<savedHeap>  JCSystem.isTransient(dest) != JCSystem.NOT_A_TRANSIENT_OBJECT ==>
                !\backup(\transactionUpdated(dest));
           ensures<savedHeap> (\forall short i; i>=0 && i<length; \backup(dest[destOffset + i]) == 
                 (JCSystem.isTransient(dest) == JCSystem.NOT_A_TRANSIENT_OBJECT ?  
                    \old(\backup(dest[destOffset + i]))
                  : \old(src[srcOffset + i]))
              );
           signals (NullPointerException npe) npe == JCSystem.npe && (src == null || dest == null);
           signals (ArrayIndexOutOfBoundsException aioobe) aioobe == JCSystem.aioobe && (length < 0 ||
               srcOffset < 0 || destOffset < 0 ||
               srcOffset + length > src.length || destOffset + length > dest.length);
           signals_only NullPointerException, ArrayIndexOutOfBoundsException;
           assignable<heap><savedHeap> dest[destOffset..destOffset+length-1];
           assignable<savedHeap> \transactionUpdated(dest);
      @*/
    public static final short arrayCopy(/*@ nullable @*/ byte[] src, short srcOffset,
            /*@ nullable @*/ byte[] dest, short destOffset, short length)
            throws NullPointerException, ArrayIndexOutOfBoundsException {

        if (src == null || dest == null)
            throw JCSystem.npe;
        if (length < 0 || srcOffset < 0 || destOffset < 0
                || srcOffset  > (short)(src.length - length)
                || destOffset > (short)(dest.length - length))
            throw JCSystem.aioobe;

        if(src == dest && srcOffset == destOffset) {
          return (short) (destOffset + length);
        }
        final boolean startTransaction = (JCSystem.getTransactionDepth() == 0);
        if(startTransaction) {
          JCSystem.beginTransaction();
        }
        if(src != dest || srcOffset > destOffset) {
          /*@
             loop_invariant i >= 0 && i <= length &&
                srcOffset + i >= 0 && srcOffset + i <= src.length &&
                destOffset + i >= 0 && destOffset + i <= dest.length 
               &&
               (\forall short j; j >= 0 && j< length;
                   dest[destOffset + j] == (j<i ? \old(src[srcOffset + j]) : \old(dest[destOffset + j]))
               )
             ;
             loop_invariant<savedHeap> true 
                &&
               ((JCSystem.isTransient(dest) == JCSystem.NOT_A_TRANSIENT_OBJECT && i != 0)  ==> \backup(\transactionUpdated(dest))) 
                &&
               (JCSystem.isTransient(dest) != JCSystem.NOT_A_TRANSIENT_OBJECT ==> !\backup(\transactionUpdated(dest))) 
                &&
               (startTransaction ||
                 (\forall short j; j >= 0 && j < length; 
                  \backup(dest[destOffset + j]) ==
                    ((j >= i || JCSystem.isTransient(dest) == JCSystem.NOT_A_TRANSIENT_OBJECT) ?
                        \old(\backup(dest[destOffset + j])) :
                        \old(src[srcOffset + j]))
                 )
                )
             ;
             decreases length - i;
             assignable<heap><savedHeap> dest[destOffset..destOffset+length-1];
             assignable<savedHeap> \transactionUpdated(dest);
          @*/
          for(short i=0;i<length;i++) {
              dest[destOffset + i] = src[srcOffset + i];
          }
        }else{
          /*@
             loop_invariant i >= 0 && i <= length &&
                srcOffset + length - i >= 0 && srcOffset + length - i  <= src.length &&
                destOffset + length - i >= 0 && destOffset + length - i <= dest.length
                &&
                (\forall short j; j >= 0 && j < length; 
                    dest[destOffset + j] == (j >= length - i ? \old(src[srcOffset + j]) : \old(dest[destOffset + j]))
                )
             ;
             loop_invariant<savedHeap>
                ((JCSystem.isTransient(dest) == JCSystem.NOT_A_TRANSIENT_OBJECT && i != 0)  ==> \backup(\transactionUpdated(dest))) &&
               (JCSystem.isTransient(dest) != JCSystem.NOT_A_TRANSIENT_OBJECT ==> !\backup(\transactionUpdated(dest))) 
                &&
               (startTransaction || 
                 (\forall short j; j >= 0 && j < length; 
                  \backup(dest[destOffset + j]) ==
                    ((j < length - i || JCSystem.isTransient(dest) == JCSystem.NOT_A_TRANSIENT_OBJECT) ?
                       \old(\backup(dest[destOffset + j])) :
                        \old(src[srcOffset + j]))
                 )
               )
               ;
             decreases length - i;
             assignable<heap><savedHeap> dest[destOffset..destOffset+length-1];
             assignable<savedHeap> \transactionUpdated(dest);
          @*/
          for(short i=0; i<length; i++) {
            dest[destOffset + (length - 1) - i] = src[srcOffset + (length - 1) - i];
          }
        }
        if(startTransaction) {
          JCSystem.commitTransaction();
        }
        return (short) (destOffset + length);
    }

    /*@
         public behavior
           requires JCSystem.npe != null;
           requires JCSystem.aioobe != null;
           ensures \result == -1 || \result == 0 || \result == 1;
           ensures \result == 0 ==> (\forall short i; i>=0 && i < length; src[srcOffset + i] == dest[destOffset + i]);
           ensures \result == -1 ==>
              (\exists short i; i>=0 && i < length; src[srcOffset + i] < dest[destOffset + i] &&
                 (\forall short j; j>=0 && j<i; src[srcOffset + j] == dest[destOffset + j]));
           ensures \result == 1 ==>
              (\exists short i; i>=0 && i < length; src[srcOffset + i] > dest[destOffset + i] &&
                 (\forall short j; j>=0 && j<i; src[srcOffset + j] == dest[destOffset + j]));
           signals (NullPointerException npe) npe == JCSystem.npe && (src == null || dest == null);
           signals (ArrayIndexOutOfBoundsException aioobe) aioobe == JCSystem.aioobe && (length < 0 ||
               srcOffset < 0 || destOffset < 0 ||
               srcOffset + length > src.length || destOffset + length > dest.length);
           signals_only NullPointerException, ArrayIndexOutOfBoundsException;
           assignable \strictly_nothing;
    @*/
    public static final byte arrayCompare(/*@ nullable @*/ byte[] src, short srcOffset,
            /*@ nullable @*/ byte[] dest, short destOffset, short length)
            throws NullPointerException, ArrayIndexOutOfBoundsException {
         if (src == null || dest == null)
            throw JCSystem.npe;
         if (length < 0 || srcOffset < 0 || destOffset < 0
                || srcOffset  > (short)(src.length - length)
                || destOffset > (short)(dest.length - length))
            throw JCSystem.aioobe;

        if(src == dest && srcOffset == destOffset) {
          return (byte)0;
        }

        /*@ loop_invariant i>=0 && i <= length &&
               (\forall short j; j>=0 && j < i; src[srcOffset + j] == dest[destOffset + j]);
            decreases length - i;
            assignable \strictly_nothing;
          @*/
        for(short i=0; i<length; i++) {
           if(src[srcOffset + i] < dest[destOffset + i]) {
              return (byte)-1;
           }
           if(src[srcOffset + i] > dest[destOffset + i]) {
              return (byte)1;
           }
        }
        return (byte)0;
    }


    /*@ public behavior
           requires JCSystem.npe != null;
           requires JCSystem.aioobe != null;
           requires<savedHeap>
             JCSystem.isTransient(bArray) != JCSystem.NOT_A_TRANSIENT_OBJECT
                ==> !\transactionUpdated(bArray);
           ensures \result == bOffset + length;
           ensures (\forall short i; i>=0 && i<length; bArray[bOffset + i] == value);
           ensures<savedHeap> (\forall short i; i>=0 && i<length;
              \backup(bArray[bOffset + i]) == 
                ((JCSystem.isTransient(bArray) == JCSystem.NOT_A_TRANSIENT_OBJECT
                  && \backup(\transactionUpdated(bArray))) ?  
                    \old(\backup(bArray[bOffset + i]))
                  : value)
              );
           signals (NullPointerException npe)
               npe == JCSystem.npe && (bArray == null);
           signals (ArrayIndexOutOfBoundsException aioobe)
               aioobe == JCSystem.aioobe && (length < 0 ||
               bOffset < 0 || 
               bOffset + length > bArray.length);
           signals_only NullPointerException, ArrayIndexOutOfBoundsException;
           assignable<heap><savedHeap> bArray[bOffset..bOffset+length-1]; @*/
    public static final short arrayFillNonAtomic(/*@ nullable @*/ byte[] bArray, short bOffset,
            short length, byte value)
            throws NullPointerException, ArrayIndexOutOfBoundsException {

        if (bArray == null)
            throw JCSystem.npe;
        if (length < 0 || bOffset < 0 
                || bOffset  > (short)(bArray.length - length))
            throw JCSystem.aioobe;

        final boolean changeTransient =
          (JCSystem.nativeKeYGetTransient(bArray) == JCSystem.NOT_A_TRANSIENT_OBJECT);
        if(changeTransient) {
          JCSystem.nativeKeYSetTransient(bArray, JCSystem.CLEAR_ON_RESET);
        }

          /*@
             loop_invariant i >= 0 && i <= length &&
                bOffset + i >= 0 && bOffset + i <= bArray.length &&
               (\forall short j; j >= 0 && j< length;
                   bArray[bOffset + j] == (j<i ? value : \old(bArray[bOffset + j]))
               )
             ;
             loop_invariant<savedHeap>
               (\forall short j; j >= 0 && j < length; 
                  \backup(bArray[bOffset + j]) ==
                    ((j >= i || \backup(\transactionUpdated(bArray))) ?
                        \old(\backup(bArray[bOffset + j])) :
                        value)
               );
             decreases length - i;
             assignable<heap><savedHeap> bArray[bOffset..bOffset+length-1];
          @*/
          for(short i=0;i<length;i++) {
              bArray[bOffset + i] = value;
          }
        if(changeTransient) {      
          JCSystem.nativeKeYSetTransient(bArray, JCSystem.NOT_A_TRANSIENT_OBJECT);
        }
        return (short) (bOffset + length);
    }

}
