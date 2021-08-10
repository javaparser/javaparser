class MySubclass extends MyClass {
    /*@ ensures modelField == \old(modelField) + 2;
      @ assignable x, y;
      @*/
    void changeModelField() {
        x++;
        y++;
    }

    Object o;

    //@ represents footprint = \storeref(this.*, o.*);


    int add27(int i) {
        return attr = 27 + i;
    }


    int x;
    int y;
    //@ model int modelField;    
    //@ represents modelField = x + y;
    int test;


}
