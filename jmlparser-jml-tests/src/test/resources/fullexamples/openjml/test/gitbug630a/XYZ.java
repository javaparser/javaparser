    public class XYZ {
        //@ private exceptional_behavior
        //@     signals (IndexOutOfBoundsException ex) true;
        private static void callMe() {
            throw new IndexOutOfBoundsException();
        }
        //@ private behavior
        //@     ensures true;
        private static boolean convertException() {
            try {
                callMe();
            } catch (IndexOutOfBoundsException ex) {
                throw new ArrayIndexOutOfBoundsException(((Object)ex).toString());
            }
            return true;
        }
    }
