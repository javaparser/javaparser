package junit4.zoo.builders;

import com.example.zoo.sdk.internal.*;

import static junit4.zoo.constants.ZooTestConstants.*;

@SuppressWarnings("unused")
public class ElephantBuilder {

    private Elephant apiObject = new Elephant();

    public ElephantBuilder lionID(String lionID) {
        apiObject.setTaskID(lionID);
        apiObject.setDocObjCode(Lion.OBJCODE);
        apiObject.setObjID(lionID);
        return this;
    }
}
