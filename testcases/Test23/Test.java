public class Test {
    static class Node {
        int value;
        Node next;

        Node(int v) {
            this.value = v;
        }
    }

    static Node[] pool = new Node[5000];

    static int heavy(Node head) {
        int sum = 0;
        Node p = head;

        for (int i = 0; i < 20000; i++) {
            int a = p.value;
            int b = p.value;
            int c = p.value;
            sum += a + b + c;

            if ((i & 1) == 0) {
                int d = p.value;
                int e = p.value;
                sum += d + e;
            } else {
                int f = p.value;
                int g = p.value;
                sum += f + g;
            }

            if (p.next != null) {
                p = p.next;
            }
        }

        return sum;
    }

    static Node buildList(int n) {
        Node head = new Node(1);
        Node cur = head;

        for (int i = 2; i <= n; i++) {
            Node t = new Node(i);
            cur.next = t;
            cur = t;
        }

        return head;
    }

    public static void main(String[] args) {
        for (int i = 0; i < pool.length; i++) {
            pool[i] = new Node(i);
        }

        Node head = buildList(2000);
        int result = 0;

        for (int i = 0; i < 50; i++) {
            result += heavy(head);
        }

        System.out.println(result);
    }
}