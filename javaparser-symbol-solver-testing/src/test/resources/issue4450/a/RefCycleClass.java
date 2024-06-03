package a;

import static a.RefCycleEnum.*;
import static a.RefClass2.*;

public class RefCycleClass {

    public static int value1Value = 1;

    private RefCycleEnum theEnum;

    public void runMe() {
        unknownName.run();
        RefCycleEnum myEnum = Value1;
    }
}
