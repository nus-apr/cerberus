package wronglock2;

import com.facebook.infer.annotation.*;

@ThreadSafe
public class Main implements Runnable {

    public static Struct s = new Struct(1, 0);
    
    public static int THREADS = 5;

    public static void main(String[] args) throws Exception {
        Thread[] t = new Thread[THREADS];

        for (int i = 0; i < THREADS; i++) {
            t[i] = new Thread(new Main());
            t[i].start();
        }
        for (int i = 0; i < THREADS; i++) {
            t[i].join();
        }

        if (s.getCount() != THREADS) {
            throw new Exception("bug found.");
        }
    }

    @Override
    public void run() {

        s = new Struct(s.getNumber() * 2, s.getCount() + 1);

    }

    public static class Struct {
        int number;
        int count;

        public Struct(int number, int count) {
            this.number = number;
            this.count = count;
        }

        public int getNumber() {
            return number;
        }

        public int getCount() {
            return count;
        }
    }
}
