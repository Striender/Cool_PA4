public class Test {
    int f_written_only;
    int f_read;
    int f_never_used;
    public static void main(String[] args) {
        Test t = new Test();
        t.f_written_only = 42;
        t.f_read = 10;
        int x = t.f_read;
    }
}
