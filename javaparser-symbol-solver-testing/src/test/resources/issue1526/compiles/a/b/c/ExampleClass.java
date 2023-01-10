package a.b.c;

import d.e.f.DataObjectFactory;

public class ExampleClass {

    protected final DataObjectFactory doFactory;


    public ExampleClass() {
        doFactory = null;
    }


    public DataObject getDataObject(String objectID) {
        return doFactory.getDataObject(objectID);
    }

}
