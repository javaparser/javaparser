import org.jmlspecs.models.JMLObjectSequence;
//@ model import org.jmlspecs.models.JMLObjectSequence;
class Sequence {
private Object[] elems;
private int size;
//@ model instance JMLObjectSequence theSequence;
//@ private represents theSequence <- abstractionFunction();
private /*@ pure helper @*/ JMLObjectSequence abstractionFunction () {
return JMLObjectSequence.convertFrom(elems, size);
}
Sequence() { elems = new Object[2]; }
public static void main(String[] args) { Sequence s = new Sequence(); }
}