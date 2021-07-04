public class DayTimeMain {

public static void main(String[] args) {
        DayTime start = new DayTime(6, 5, 30),
                stop = new DayTime(7, 5, 45);
        int diff;

        System.out.printf("SECONDS DIFFERENCE: %d:%d:%d - ", start.hour(), start.minute(), start.second());
        System.out.printf("%d:%d:%d ", stop.hour(), stop.minute(), stop.second());
        System.out.printf("= %d:\n", start.diffSeconds(stop));
    }
}
