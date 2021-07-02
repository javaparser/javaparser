package MapCaseStudy;

/**
 * This is a simple test for {@link MapImplementation}, to see if it works as
 * expected.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class TestImplementation {

    static MapInterface map = new MapImplementation();
    static Object key = new Object();
    static Object value = new Object();
    static int errors = 0;

    static void test(boolean containsKey, boolean containsValue, Object get, int size, boolean isEmpty) {
        if (map.containsKey(key) != containsKey) errors++;
        if (map.containsValue(value) != containsValue) errors++;
        if (map.get(key) != get) errors++;
        if (map.size() != size) errors++;
        if (map.isEmpty() != isEmpty) errors++;
    }

    public static void main(String[] args) {
        
        test(false, false, null, 0, true);
        map.put(key, value);
        test(true, true, value, 1, false);
        map.clear();
        test(false, false, null, 0, true);
        map.put(key, value);
        test(true, true, value, 1, false);
        map.remove(key);
        test(false, false, null, 0, true);
        
        if (errors == 0) {
            //System.out.println("The map works as expected.");
        } else {
            //System.out.println("Unexpected map behaviour.");
        }
    }

}
