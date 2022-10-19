 
 class HelloHelper { 
   Object l = new Object(); 
   Object p = new Object(); 
   Object GlobalLock = new Object(); 
  
   private String sharedString = null;  
  
   private static void busyWait() { 
     long i = 1; 
     while (i < 2000000000) { i++; } 
     return;  
   } 
  
   public void t1() { 
     synchronized(l) {
       System.out.println("T1 got lock l"); 
       busyWait(); 
  
         sharedString = "Hello World-1 "; 
         busyWait();  
         sharedString = sharedString + "from T1"; 
         System.out.println(sharedString);  
  
       System.out.println("T1 released lock l");  
     }
    
   } 
  
  
   public void t2() {
    synchronized(p) {
       System.out.println("T2 got lock p"); 
       busyWait(); 
  
         sharedString = "Hello World-2 "; 
         busyWait();  
         sharedString = sharedString + "from T2"; 
         System.out.println(sharedString);  
  
       System.out.println("T2 released lock p");  
     }        
          
   } 
  
   public void t3() { 
     synchronized(GlobalLock) { 
       System.out.println("T3 got lock G"); 
       busyWait(); 
  
       synchronized(p) { 
         System.out.println("T3 got lock p");        
         synchronized(l) { 
           System.out.println("T3 got lock l");        
  
           sharedString = "Hello World-3 "; 
           busyWait();  
           sharedString = sharedString + "from T3"; 
           System.out.println(sharedString);  
  
           System.out.println("T3 released lock l");  
         } 
         System.out.println("T3 released lock p");  
       } 
       System.out.println("T3 released lock G");  
     }       
   } 
  
 }  
  
 public class Hello { 
    public static void main(String[] args){ 
       HelloHelper h = new HelloHelper(); 
  
       Thread thread1 = new Thread(){ public void run() { h.t1(); } }; 
       Thread thread2 = new Thread(){ public void run() { h.t2(); } }; 
       Thread thread3 = new Thread(){ public void run() { h.t3(); } }; 
  
       thread1.start(); 
       thread2.start(); 
       thread3.start(); 
    } 
 }