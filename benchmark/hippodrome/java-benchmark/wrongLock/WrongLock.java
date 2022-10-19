package wrongLock;

import com.facebook.infer.annotation.*;
/**
 * @author Xuan
 * Created on 2005-1-18
 * <p>
 * This class simulates the wrong lock bug
 * Method A requests a lock on data while method B request a lock
 * on the class.
 */
@ThreadSafe
public class WrongLock {
    Data data;

    public WrongLock(Data data) {
        this.data = data;
    }

    public void A() {
        synchronized (data) {
            int x = data.value;
            data.value++;
            //assert (data.value==x+1);
            if (data.value != (x + 1))
                throw new RuntimeException("bug found");
        }
    }

    public void B() {
        synchronized (this) {
            data.value++;
        }
    }
}
