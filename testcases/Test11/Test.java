class A {
    A f;
}

class B extends A {
}

public class Test {
    public static void main(String[] args) {
        B b = new B();
        b.f = new A();

        A x = b.f;
        A y = b.f;   // REDUNDANT
    }
}
