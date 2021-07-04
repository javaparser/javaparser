/*IN PROGRESS - NOT FOR DISTRIBUTION*/
import javax.swing.text.Segment;

/**
 * A driver program to exercise the functionality of  
 * java.lang.AbstractStringBuilder and 
 * java.lang.StringBuilder 
 * 
 * @author Mike Rawding
 */
public class StringBuilderDriver {
    


    
    //private static final char[] testCharArray = {'t', 'e', 's', 't'};
    //private static final String testString = "Test String";
    //private static final char[] nullCharArray = null;
    //private static final String nullString = null;
    //private static final Object nullObject = null;
    

    public static void main(String[] args) {
        
        testConstructorVoid(); //1
        
        testConstructorInt(); //2 
        
        testLength(); //3
        
        testCapacity(); //4
        
        testEnsureCapacity(); //5
        
        testTrimToSize(); //9
        
        testSetLength(); //10
        
        testCharAt(); //11
        
        testCodePointAt(); //12
        
        testCodePointBefore(); //13
        
        testCodePointCount(); //14
        
        testOffsetByCodePoints(); //15
        
        testGetChars(); //16
        
        testSetCharAt(); //17
        
        testAppendObject(); //18
        
        testAppendString(); //19
        
        testAppendStringBuffer(); //20
        
        testAppendCharSequence(); //22

        testAppendCharSequenceStartEnd(); //24
        
        testAppendCharArray(); //25
        
        testAppendCharArrayStartEnd(); //26
        
        testAppend_boolean(); //27
        
        testAppend_char(); //28
        
        testAppend_int(); //29
        
        testAppend_long(); //30
        
        testAppend_float(); //31
        
        testAppend_double(); //32
        
        testDelete(); //33
        
        testAppendCodePoint(); //34
        
        testDeleteCharAt(); //35
        
        testReplace(); //36
        
        testSubstringStart(); //37
        
        testSubSequence(); //38
        
        testSubstringStartEnd(); //39
        
        testInsertIndexCharArray(); //40
        
        testInsertObject(); //41
        
        testInsertString(); //42
        
        testInsertCharArray(); //43
        
        testInsertCharSequence(); //44
        
        testInsertCharSequenceStartEnd(); //45
        
        testInsert_boolean(); //46
        
        testInsert_char(); //47
        
        testInsert_int(); //48
        
        testInsert_long(); //49
        
        testInsert_float(); //50
        
        testInsert_double(); //51
        
        testIndexOf(); //52
        
        testIndexOfStart(); //53
        
        testLastIndexOf(); //54
        
        testLastIndexOfStart(); //55
        
        testReverse(); //56
        
        testToString(); //58
        
        /* -- -- -- -- Methods within StringBuilder -- -- -- -- */
        
        testConstructorString(); //3
         
        System.out.println("done");    
    }
    
    private static void testConstructorVoid() { //1
        StringBuilder sb = new StringBuilder();
    }
    
    private static void testConstructorInt() { //2
        StringBuilder sb0 = new StringBuilder(0);
        StringBuilder sb1 = new StringBuilder(1);
        try {
            StringBuilder sb2 = new StringBuilder(-1);
        } catch (NegativeArraySizeException ex) {
            System.out.println("StringBuilder(-1) correctly threw an exception.");
        }
    }
    
    private static void testLength() { //3
        StringBuilder sb0 = new StringBuilder("Test String");
        StringBuilder sb1 = new StringBuilder(0);
        sb0.length();
        sb1.length();
    }
    
    private static void testCapacity() { //4
        StringBuilder sb0 = new StringBuilder("Test String");
        StringBuilder sb1 = new StringBuilder(0);
        sb0.capacity();
        sb1.capacity();
    }
    
    private static void testEnsureCapacity() { //5
        StringBuilder sb = new StringBuilder("Test String");
        sb.ensureCapacity(-1);
        sb.ensureCapacity(4);
        sb.ensureCapacity(1000);
    }
    
    //private method //6
    
    //private method //7
    
    //private method //8
    
    private static void testTrimToSize() { //9
        StringBuilder sb = new StringBuilder(); //capacity 16, count 0
        //@ assert sb.stringLength <= sb.value.length;
        sb.trimToSize();
        StringBuilder sb1 = new StringBuilder();
        //@ show sb1.count, sb1.capacity, sb1.value.length;
        sb1.append("sixteencharacter"); //capacity 16, count 16;
        //@ show sb1.count, sb1.capacity, sb1.value.length;
        sb1.trimToSize();
    }
    
    private static void testSetLength() { //10
        StringBuilder stringBuilder = new StringBuilder("StringBuilder");
        stringBuilder.setLength(100);
        stringBuilder.setLength(4);
        stringBuilder.setLength(0);
        try {
            stringBuilder.setLength(-1);
        } catch (StringIndexOutOfBoundsException ex) {
            System.out.println("setLength(-1) correctly threw an exception.");
        }
    }
    
    private static void testCharAt() { //11
        StringBuilder stringBuilder = new StringBuilder("012345");
        stringBuilder.charAt(0);
        stringBuilder.charAt(5);
        try {
            stringBuilder.charAt(-1);
        } catch (StringIndexOutOfBoundsException ex) {
            System.out.println("charAt(-1) correctly threw an exception.");
        }
        try {
            stringBuilder.charAt(6);            
        } catch (StringIndexOutOfBoundsException ex) {
            System.out.println("setLength(6) (too large) correctly threw an exception.");
        }
    }
    
    public static void testCodePointAt() { //12
        
    }
    
    public static void testCodePointBefore() { //13
        
    }
    
    public static void testCodePointCount() { //14
        
    }
    
    public static void testOffsetByCodePoints() { //15
        
    }
    //TODO - look over this
    private static void testGetChars() { //16
        char[] dst = new char[2];
        StringBuilder stringBuilder = new StringBuilder("Test String");
        try {
            stringBuilder.getChars(0, 1, dst, 0);
        } catch (ArrayIndexOutOfBoundsException ex) {
            System.out.println("getChars() correctly threw an exception.");
        }
    }    
    
    private static void testSetCharAt() { //17
        
    }
    
    private static void testAppendObject() { //18
        Integer testInteger = new Integer(1);
        /*@ nullable @*/Integer nullInteger = null;
        
        StringBuilder stringBuilder = new StringBuilder("foo");
        
        stringBuilder.append(testInteger);
        stringBuilder.append(nullInteger);
    }
    
    private static void testAppendString() { //19
        String testString = "Test";
        String emptyString = "";
        /*@ nullable @*/ String nullString = null;
        
        StringBuilder stringBuilder = new StringBuilder();
        
        stringBuilder.append(testString);
        //stringBuilder.append(emptyString); //TODO - failure
        stringBuilder.append(nullString);
    }

    private static void testAppendStringBuffer() {//20
        //TODO - StringBuffer fails ESC, so cannot use it in testing
//        StringBuilder sb0 = new StringBuilder();
//        StringBuffer stringBuffer = new StringBuffer();
//        sb0.append("String");
//        /*@ nullable @*/StringBuffer nullStringBuffer = null;
//        sb0.append(nullStringBuffer);
    }
    
    //package method append(AbstractStringBuilder) //21

    private static void testAppendCharSequence() { //22
        char[] testCharArray = {'t', 'e', 's', 't'};
        Segment testSequence = new Segment(testCharArray, 0, testCharArray.length);
        char[] emptyCharArray = {};
        Segment emptySegment = new Segment(emptyCharArray, 0, emptyCharArray.length);
        /*@ nullable @*/Segment nullSegment = null;
        
        StringBuilder stringBuilder = new StringBuilder();
        
        stringBuilder.append(testSequence);
        //stringBuilder.append(emptySegment);
        stringBuilder.append(nullSegment);
    }
    
    //private method appendNull(); //23
    
    private static void testAppendCharSequenceStartEnd() { //24
        char[] testCharArray = {'t', 'e', 's', 't'};
        Segment testSequence = new Segment(testCharArray, 0, testCharArray.length);
        char[] emptyCharArray = {};
        Segment emptySegment = new Segment(emptyCharArray, 0, emptyCharArray.length);
        /*@ nullable @*/Segment nullSegment = null;
        
        StringBuilder stringBuilder = new StringBuilder();
        
        stringBuilder.append(testSequence, 0, testSequence.length());
        stringBuilder.append(emptySegment, 0, emptySegment.length());
        stringBuilder.append(nullSegment, 0, 0);
    }

    private static void testAppendCharArray() { //25
        char[] testCharArray = {'t', 'e', 's', 't'};
        char[] emptyCharArray = {};
        
        StringBuilder stringBuilder = new StringBuilder();
        
        stringBuilder.append(testCharArray);
        stringBuilder.append(emptyCharArray);
    }

    private static void testAppendCharArrayStartEnd() { //26
        char[] testCharArray = {'t', 'e', 's', 't'};
        char[] emptyCharArray = {};
        ///*@ nullable @*/char[] nullCharArray = null;
        
        StringBuilder stringBuilder = new StringBuilder();
        
        stringBuilder.append(testCharArray, 0, testCharArray.length);
        stringBuilder.append(emptyCharArray, 0, emptyCharArray.length);
        //stringBuilder.append(nullCharArray, 0, 0); //TODO - this throws
    }
    
    private static void testAppend_boolean() { //27
        StringBuilder stringBuilder = new StringBuilder();
        
        stringBuilder.append(true);
        stringBuilder.append(false);
    }
    
    private static void testAppend_char() { //28
        StringBuilder stringBuilder = new StringBuilder();
        
        stringBuilder.append('a');
        stringBuilder.append('1');
    }
    
    private static void testAppend_int() { //29
        StringBuilder stringBuilder = new StringBuilder();
        
        stringBuilder.append(-1);
        stringBuilder.append(0);
        stringBuilder.append(1);
    }
    
    private static void testAppend_long() { //30
        StringBuilder stringBuilder = new StringBuilder();
        
        stringBuilder.append(-1L);
        stringBuilder.append(0L);
        stringBuilder.append(1L);
    }
    
    private static void testAppend_float() { //31
        StringBuilder stringBuilder = new StringBuilder();
        
        stringBuilder.append(-1.0f);
        stringBuilder.append(0f);
        stringBuilder.append(1.5f);
    }        
    

    private static void testAppend_double() { //32
        //TODO - trouble with doubles during ESC
//        StringBuilder stringBuilder = new StringBuilder();
//        
//        stringBuilder.append(1.0);
//        stringBuilder.append(0);
//        stringBuilder.append(1.5);
    }

    private static void testDelete() { //33
//        StringBuilder stringBuilder = new StringBuilder("Test Sting");
//        stringBuilder.delete(0, 0);
//        stringBuilder.delete(0, 1);
//        stringBuilder.delete(-1, 4);
//        stringBuilder.delete(0, 100);
    }

    private static void testAppendCodePoint() { //34 
        //TODO check spec
//        StringBuilder stringBuilder = new StringBuilder();
//        
//        stringBuilder.appendCodePoint(-1);
//        stringBuilder.appendCodePoint(0);
//        stringBuilder.appendCodePoint(1);
    }

    private static void testDeleteCharAt() { //35
//        StringBuilder stringBuilder = new StringBuilder("Test Sting");
//        
//        stringBuilder.deleteCharAt(0);
//        stringBuilder.deleteCharAt(1);
//        //stringBuilder.deleteCharAt(-1);
//        //stringBuilder.deleteCharAt(100);
    }
    
    private static void testReplace() { //36
        StringBuilder stringBuilder = new StringBuilder("Test String");
        stringBuilder.replace(0, 1, "foo");
        
        try {
            stringBuilder.replace(-1, 1, "foo");
        } catch (StringIndexOutOfBoundsException ex) {
            System.out.println("replace() with negative start correctly threw an exception");
        }
        
    }
    
    private static void testSubstringStart() { //37
        StringBuilder sb = new StringBuilder("Test String");
        sb.substring(0);
        sb.substring(1);
        sb.substring(sb.length());
        
        try {
            sb.substring(-1);
        } catch (StringIndexOutOfBoundsException ex) {
            System.out.println("substring() with negative start correctly threw an exception");
        }
        
        try {
            sb.substring(100);
        } catch (StringIndexOutOfBoundsException ex) {
            System.out.println("substring() with start too large correctly threw an exception");
        }
    }
    
    private static void testSubSequence() { //38
        StringBuilder sb = new StringBuilder("Test String");
        sb.subSequence(0, 1);
        sb.subSequence(1, 1);
        
        try {
            sb.subSequence(-1, 0);
        } catch (StringIndexOutOfBoundsException ex) {
            System.out.println("subSequence() with negative start correctly threw an exception");
        }
        
        try {
            sb.subSequence(1, 0);
        } catch (StringIndexOutOfBoundsException ex) {
            System.out.println("subSequence() with start < end correctly threw an exception");
        }
        
        try {
            sb.subSequence(1, 100);
        } catch (StringIndexOutOfBoundsException ex) {
            System.out.println("subSequence() with end too large correctly threw an exception");
        }
    }
    
    private static void testSubstringStartEnd() { //39
        StringBuilder sb = new StringBuilder("Test String");
        sb.substring(0, 1);
        sb.substring(1, 1);
        
        try {
            sb.substring(-1, 0);
        } catch (StringIndexOutOfBoundsException ex) {
            System.out.println("substring() with negative start correctly threw an exception");
        }
        
        try {
            sb.substring(1, 0);
        } catch (StringIndexOutOfBoundsException ex) {
            System.out.println("substring() with start < end correctly threw an exception");
        }
        
        try {
            sb.substring(1, 100);
        } catch (StringIndexOutOfBoundsException ex) {
            System.out.println("substring() with end too large correctly threw an exception");
        }
    }
    
    private static void testInsertIndexCharArray() { //40
        StringBuilder sb = new StringBuilder("Test String");
        char[] charArray = {'t', 'e', 's', 't'};
        /*@ nullable @*/ char[] nullCharArray = null;
        
        sb.insert(0, charArray, 0, 3);
        sb.insert(0, charArray, 0, 0);
        
        try {
            sb.insert(-1, charArray, 0, 0);
        } catch (StringIndexOutOfBoundsException ex) {
            System.out.println("insert() with negative index correctly threw an exception");
        }
        
        try {
            sb.insert(-1, charArray, 0, 0);
        } catch (StringIndexOutOfBoundsException ex) {
            System.out.println("insert() with negative index correctly threw an exception");
        }
        
        try {
            sb.insert(100, charArray, 0, 0);
        } catch (StringIndexOutOfBoundsException ex) {
            System.out.println("insert() with index > stringLength correctly threw an exception");
        }
        
        try {
            sb.insert(0, charArray, -1, 0);
        } catch (StringIndexOutOfBoundsException ex) {
            System.out.println("insert() with negative offset correctly threw an exception");
        }
        
        try {
            sb.insert(0, charArray, 1, -1);
        } catch (StringIndexOutOfBoundsException ex) {
            System.out.println("insert() with negative len correctly threw an exception");
        }
        
        try {
            sb.insert(0, charArray, 1, 100);
        } catch (StringIndexOutOfBoundsException ex) {
            System.out.println("insert() with len too large correctly threw an exception");
        }
        
        try {
            sb.insert(0, nullCharArray, 0, 0);
        } catch (NullPointerException ex) {
            System.out.println("insert() with null char[] correctly threw an exception");
        }
        
    }
    
    private static void testInsertObject() { //41
        StringBuilder sb = new StringBuilder("Test String");
        Integer integer = new Integer(1);
        /*@ nullable @*/Object nullObject = null;
        
        sb.insert(0, integer);
        sb.insert(sb.length(), integer);
        sb.insert(0, nullObject);
        
        try {
            sb.insert(-1, integer);
        } catch (StringIndexOutOfBoundsException ex) {
            System.out.println("insert() with negative offset correctly threw an exception");
        }
        
        try {
            sb.insert(100, integer);
        } catch (StringIndexOutOfBoundsException ex) {
            System.out.println("insert() with offset too large correctly threw an exception");
        }

        
    }

    private static void testInsertString() { //42
        StringBuilder sb = new StringBuilder("Test StringBuilder");
        String string = "Test String";
        /*@ nullable @*/String nullString = null;
        
        sb.insert(0, string);
        sb.insert(sb.length(), string);
        sb.insert(0, nullString);
        
        try {
            //sb.insert(-1, string);//TODO - this fails under ESC
        } catch (StringIndexOutOfBoundsException ex) {
            System.out.println("insert() with negative offset correctly threw an exception");
        }
        
        try {
            //sb.insert(sb.length() + 1, string); //TODO ESC failure
        } catch (StringIndexOutOfBoundsException ex) {
            System.out.println("insert() with offset too large correctly threw an exception");
        }
    }
    
    private static void testInsertCharArray() { //43
        StringBuilder sb = new StringBuilder("Test String");
        char[] charArray = {'t', 'e', 's', 't'};
        /*@ nullable @*/ char[] nullCharArray = null;
        
        
        sb.insert(0, charArray);
        sb.insert(sb.length(), charArray);
        
        try {
            sb.insert(-1, charArray);
        } catch (StringIndexOutOfBoundsException ex) {
            System.out.println("insert() with negative offset correctly threw an exception");
        }
        
        try {
            sb.insert(sb.length() + 1, charArray, 0, 0);
        } catch (StringIndexOutOfBoundsException ex) {
            System.out.println("insert() with offest too large correctly threw an exception");
        }
        
        try {
            sb.insert(0, nullCharArray);
        } catch (NullPointerException ex) {
            System.out.println("insert() with null char[] correctly threw an exception");
        }

    }
    
    private static void testInsertCharSequence() { //44
        
    }
    
    private static void testInsertCharSequenceStartEnd() {//45
        
    }

    private static void testInsert_boolean() { //46
        
    }
    
    private static void testInsert_char() { //47
        
    }
    
    private static void testInsert_int() { //48
        
    }
    
    private static void testInsert_long() { //49
        
    }

    private static void testInsert_float() { //50
        
    }

    private static void testInsert_double() { //51
        
    }

    private static void testIndexOf() { //52
        StringBuilder sb = new StringBuilder("Test String");
        String target = "Test";
        /*@ nullable @*/String nullString = null;
        
        sb.indexOf("Test");
        sb.indexOf("foo");
        
        try {
            sb.indexOf(nullString);            
        } catch (NullPointerException ex) {
            System.out.println("testIndexOf() with null String correctly threw an exception");
        }

        
    }
    
    private static void testIndexOfStart() { //53
        
    }
    
    private static void testLastIndexOf() { //54
        
    }
    
    private static void testLastIndexOfStart() { //55
        
    }
    
    private static void testReverse() { //56
        
    }
    
    //private method 57
    
    private static void testToString() { //58
        
    }
    
    //package method 58
    
    private static void testConstructorCharSequence() { //4
        char[] emptyCharArray = {};
        char[] charArray = {'t', 'e', 's', 't'};
        
        Segment voidSegment = new Segment();
        Segment emptySegment = new Segment(emptyCharArray, 0, emptyCharArray.length);
        Segment segment = new Segment(charArray, 0, charArray.length);
        
        StringBuilder sb0 = new StringBuilder(voidSegment);
        StringBuilder sb1 = new StringBuilder(emptySegment);
        StringBuilder sb2 = new StringBuilder(segment);

        try {
            /*@ nullable @*/Segment nullSegment = null;
            StringBuilder sb3 = new StringBuilder(nullSegment);
        } catch (NullPointerException ex) {}
    }
    
    /* -- -- -- -- Methods within StringBuilder -- -- -- -- */
    private static void testConstructorString() { //3
        StringBuilder sb0 = new StringBuilder("");
        StringBuilder sb1 = new StringBuilder("StringBuilder");
        try {
            /*@ nullable @*/String nullString = null;
            StringBuilder sb3 = new StringBuilder(nullString);
        } catch (NullPointerException ex) {}
    }
    

}