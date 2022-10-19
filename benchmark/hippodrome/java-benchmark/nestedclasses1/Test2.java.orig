 
   
       import com.facebook.infer.annotation.*;  
                
                        @ThreadSafe                        
                        class Test2 {   
      
                            @ThreadSafe   
                            class Test3{
                            A myA = new A();   
      
                            A myA1 = new A(); 
                            A myA2 = new A();   
      
                            public void haz(A a) {   
                                 myA1 = a;
                            }   
      
      
                            protected void haha(int x) {
                                myA1.f = x;
                            }   
                         }   
                        }   
                
      
                        class A { int f = 0; int i_myAThread = 1; }    