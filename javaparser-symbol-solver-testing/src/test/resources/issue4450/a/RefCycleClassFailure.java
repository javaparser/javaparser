package a;

import static a.RefClass2.*;

public class RefCycleClassFailure {
    public void runMe() {
        nonStatic.run();
    }
}