public class Test {
    public static void main(String[] args) {
        A a, b, x, y;
        a = new A();
        b = new A();

        if (a == b) {
            x = a.f1;
            A k = a.f1;
        } else {
            y = a.f1;
            A l = a.f1;
        }

        A z = a.f1;
    }
}

class A {
    public A f1;
}
