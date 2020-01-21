package a.b.c;

import d.e.f.DataObjectFactory; // Resolving imports takes precedence over within-the-same-package (commenting this line causes a compilation error!).

public class ExampleClass {

    protected final DataObjectFactory doFactory;


    public ExampleClass() {
        doFactory = null;
    }


    public DataObject getDataObject(String objectID) {
        return doFactory.getDataObject(objectID);
    }

}
