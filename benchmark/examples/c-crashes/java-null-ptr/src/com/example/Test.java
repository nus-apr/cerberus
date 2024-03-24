import java.util.UUID;
import java.io.*;

class Singleton
{
    // Initializing values of single and ID to null.
    private static Singleton single = null;
    private String ID = null;

    private Singleton()
    {
        /* Make it private, in order to prevent the
           creation of new instances of the Singleton
           class. */

        // Create a random ID
        ID = UUID.randomUUID().toString();
    }

    public static Singleton getInstance()
    {
        if (single == null)
            single = new Singleton();
        return single;
    }

    public String getID()
    {
        return this.ID;
    }
}

// Driver Code
public class TestSingleton
{
    public static void main(String[] args)
    {
        Singleton s = Singleton.getInstance();
        System.out.println(s.getID());
    }
}