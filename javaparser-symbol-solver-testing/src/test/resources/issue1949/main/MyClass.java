package main;

public class MyClass implements MyInterface {

    @Override
    public void doSomething() {
        MyInterface.super.doSomething();
    }

}
