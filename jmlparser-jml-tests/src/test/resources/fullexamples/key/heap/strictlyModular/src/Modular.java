class Other {
    // contract
    void other() { }
    final void otherFinal() { }
}

final class Final {
    void finalMethod() { }
}

class Modular {
    Other other;
    Final _final;

    private void privateMethod() { }

    //@ ensures true;
    void m() {
        privateMethod();
        _final.finalMethod();
        other.otherFinal();
        other.other();
    }
}
