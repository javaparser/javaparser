package a;

import static a.RefCycleClass.*;

public enum RefCycleEnum {
    Value1(value1Value);

    private RefCycleEnum(int value) {
    	Underlying = value;
    }

    public final int Underlying;
}
