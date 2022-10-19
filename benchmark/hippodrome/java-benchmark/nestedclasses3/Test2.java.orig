 
 import com.facebook.infer.annotation.*; 
                
                        @ThreadSafe                        
                        class Test2 {

                            A myA2 = new A();  
    
                            @ThreadSafe   
                            class Test3{

                            A myA = new A();   
      
                            A myA1 = new A();  
      
                            public void haz(A a) {
                                myA1 = a;

                            }   
      
      
                            protected void haha(int x) {
                                myA1.f = x;

                            } 
  
                                @ThreadSafe 
                                class Test4{ 
                                    A myA4 = new A(); 
  
  
                                    public void haz(A a) {
                                        myA4 = myA1;

                                    } 
  
  
                                    protected void haha(int x) { 
                                        synchronized (myA) { myA4.f = x; } 
                                    } 
  
                                } 
                         }  
    
    
                            public void hazT2(A a) {
                                myA2 = a;

                            }  
    
    
                            protected void hahaT2(int x) {
                                myA2.f = x;

                            }  
                        }   
                
      
                        class A { int f = 0; int i_myAThread = 1; }    