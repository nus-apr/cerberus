package wrongLock;

import com.facebook.infer.annotation.*;

/**
 * @author Xuan
 * Created on Apr 27, 2005
 */
@ThreadSafe
public class TClass1 extends Thread {
    WrongLock wl;
    public TClass1 (WrongLock wl) {
    	this.wl=wl;
    }
    
    public void run() {
    	wl.A();
    }
}
