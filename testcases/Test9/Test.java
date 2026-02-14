class A {
    static A g;
}

public class Test {
    public static void main(String[] args) {

        A.g = new A();

        A x = A.g;
        A y = A.g;   // Redundant

    }
}
