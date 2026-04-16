class Test {
    
    Test f1;
    A fa;

    public static void main(String[] args) {
        Test a = new Test();
        
        // Since A is non-static, create it using instance of Test
        A x = a.new A();
        a.fa = x;

        x.oA = a.new A();
        A y = x.oA;

        a.foo();

        A A2 = x.oA;    
    }

    void foo() {
         
    }

    class A {
        A oA;
    }
}
