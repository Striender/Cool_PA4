public class Test {
    Test f1;
    A fa;

    public static void main(String[] args) {

    }

    public void foo() {
        Test a = new Test();
        A x = new A();
        Test b = new Test();
        b.f1 = new Test();
        b.f1.fa = new A();
        A w = b.f1.fa;
        B objB = x.oB;
        a.fa = x;
        x.oA = new A();
        A y = x.oA;
        w.oB = a.fa.oB;
        bar(a, b, a.fa);
        A z = x.oA;
        A k = b.f1.fa;
    }

    public void bar(Test a, Test b, A x) {

    }
}

class A extends B {
    public A oA;
}

class B {
    public B oB;
}
