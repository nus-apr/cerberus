package pingpong;

/**
 *@author Golan
 * 17/10/2003
 * 12:01:25
 *@version 1.0
 */


public class BugThread extends Thread {


    BuggedProgram bg;


    /**
     *
     * @param bg
     */
    public BugThread(BuggedProgram bg) {
        this.bg = bg;
    }


    /**
     *
     */
    public void run() {
        this.ping();
    }


    /**
     *
     */
    public void ping() {
        bg.pingPong();
    }
}
