package com.foo;

/**
 * Has the same simple name as its superclass: the unqualified name "Widget"
 * must resolve to this class, not to com.foo.base.Widget.
 */
public class Widget extends com.foo.base.Widget {

    public void doSomething() {
        doSomethingMore(new Widget());
    }

    public void doSomethingMore(Widget widget) {}
}
