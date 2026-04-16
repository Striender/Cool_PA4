

public class Test {

    static class Node {
        Node f;
        Node a;
    }

    static void foo(Node x) {
        // unknown effect
    }

    public static void main(String[] args) {
        Node x = new Node();
        x.f = new Node();
        x.f.a = new Node();
        foo(x);   // <-- this causes loss of precision (⊤)
        x.f = new Node();
        Node p = x.f;   // p = bottom
        Node q = x.f;   // SHOULD NOT be marked redundant
    }
}
