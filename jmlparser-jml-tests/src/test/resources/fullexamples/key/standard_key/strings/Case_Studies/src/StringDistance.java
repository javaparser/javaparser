
public class StringDistance {

    public static int distance (String s1, String s2) {
        if (s1 == null || s2 == null)
            return -1;
        int d = 0;
        int m = s1.length();
        if (s1.length() > s2.length()) {
            m = s2.length();
        }
        for (int i = 0; i < m; ++i) {
            int f = s1.charAt(i) - s2.charAt(i);
            if (f >= 0) {
                d += f;
            } else {
                    d += -f;
            }
        }
        m = s1.length() - s2.length();
        if (m < 0)
            d -= m;
        else
            d += m;
        return d;
    }
	
}
