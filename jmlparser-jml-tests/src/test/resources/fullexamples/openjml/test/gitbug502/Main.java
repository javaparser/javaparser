public class Main {
    public static void main(String[] args) throws Exception {
        User user1 = new User();
        //@ reachable;
        user1.setAge(1);
        //@ reachable;
        int[] test = new int[-1]; //ESC should find this error
    }
    
    public static void main2(String[] args) throws Exception {
        User user1 = new User();
        int[] test = new int[-1]; //correctly marked for negative length array
        user1.setAge(1);
    }

}