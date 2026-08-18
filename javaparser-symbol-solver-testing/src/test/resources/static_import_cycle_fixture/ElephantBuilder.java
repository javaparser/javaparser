import static ZooTestConstants.*;

import java.util.Objects;

public class ElephantBuilder {

    public ElephantBuilder withLionObjCode() {
        Objects.requireNonNull(Lion.OBJCODE);
        return this;
    }
}
