/******************************************************************************/
/*                                                                            */
/*    BuggyProgram                                                            */
/*                                                                            */
/*    Submitted by Raz Ohad, 038249785                                        */
/*                                                                            */
/******************************************************************************/


// _____________________________________________________________________________
//
//    Module Name:
//	BuggyProgram
//
//    Extends:
//      None
//
//    Implements:
//      None
//
//    Inner Class Of:
//      None
//
//    Module Description:
//	This module includes handling the sample of the buggy program.
//      This "buggy program" generates and assigns a random number to a
//      specific user, and keeps track of all numbers generated.
//
//      In "real world", the application can be used for issuing lottery
//      numbers, identification numbers, passwords, and the like.
//
//      It is a multi-user, in the sense that two or more people can request
//      numbers at the same time, where each request is serviced by a thread.
//      A practical, real world example of this would be a web site.
//
//      Two possibilities could happen:
//      1) Two people get the same number.
//      2) The number generated for a particular user may not be the same
//         when the time comes to present or record the number.
// _____________________________________________________________________________


// ================================   Packege   ================================
package buggyprogram;


// ==========================   Java Imported Files   ==========================

import java.io.*;
import java.util.Random;

// ============================   Class definition   ===========================
public class BuggyProgram {

    // ==============================   Constants   ==============================
    public static final int LITTLE_CONCURRENCY = 3,
            AVERAGE_CONCURRENCY = 33,
            LOT_CONCURRENCY = 333,
            MAX_DIGITS = 3,
            INVALID = -3;
    public static final String PROGRAM_NAME = "BuggyProgram";


    // ==============================   Variables   ==============================
    protected static final StringBuffer buffer = new StringBuffer();
    protected long randomNumber = INVALID;
    protected static long[] history = null,
            generated = null,
            presented = null;
    static int numOfUsers = AVERAGE_CONCURRENCY;
    static String pattern = "None";
    // ===============================   Methods   ===============================

    // ___________________________________________________________________________
    //
    //    Name: BuggyProgram (constructor)
    //      Input:  None
    //	  Output: None
    //	  Description: The constructor.
    //                   Initializes the history array, creates users
    //                   (according to NUM_OF_USERS), and calls activeUsers,
    //                   to starts the users' running.
    // ___________________________________________________________________________

    public BuggyProgram() {
    }

    public void go() {
        int i = 0;
        User[] user = new User[numOfUsers];

        history = new long[numOfUsers];
        presented = new long[numOfUsers];
        generated = new long[numOfUsers];

        for (i = 0; i < numOfUsers; ++i) {
            history[i] = INVALID;
            presented[i] = INVALID;
            generated[i] = INVALID;
        }

        for (i = 0; i < numOfUsers; ++i) {
            user[i] = new User(i);
        }

        acivateUsers(user);

        for (i = 0; i < numOfUsers; ++i) {
            buffer.append("\nUser (" + i + ") generated " + generated[i] + ", " +
                    "presented " + presented[i] + ", and recorded " +
                    history[i]);
        }
        for (i = 0; i < numOfUsers; ++i) {
            if ((generated[i] != presented[i]) || (generated[i] != history[i]) ||
                    (presented[i] != history[i])) {
                //break;
                throw new RuntimeException("error");
            }
        }

//    if (i != numOfUsers){
//      pattern= "Weak-Reality";
//    }
    }


    // ___________________________________________________________________________
    //
    //    Name: main
    //      Input:  String array - command line arguments
    //	  Output: None
    //	  Description: Sets the buggy program, by calling the program
    //                   constructor.
    // ___________________________________________________________________________

    public static void main(String args[]) {

        long st, et;
        st = System.nanoTime();
        long tt;


        int i = 0;
        String outputFilename = null;
        FileWriter outputFile = null;

        args = new String[2];
        args[0] = "output.txt";
        args[1] = "little";

        if (args.length > 2 || args.length < 1) {
            System.out.println("Illegal arguments.");
            System.out.println("Arguments should be:");
            System.out.println("  1. The name of the output file, and");
            System.out.println("  2. Optional: Parameter of concurrency (little, " +
                    "average, lot).\n");
            System.exit(1);
        }

        outputFilename = args[0];

        if (args.length == 2) {
            if (args[1].toLowerCase().equals("little")) {
                numOfUsers = LITTLE_CONCURRENCY;
            } else {
                if (args[1].toLowerCase().equals("average")) {
                    numOfUsers = AVERAGE_CONCURRENCY;
                } else {
                    if (args[1].toLowerCase().equals("lot")) {
                        numOfUsers = LOT_CONCURRENCY;
                    } else {
                        System.out.println("Unrecognized parameter of concurrency.\n" +
                                "Should be: little, average, or lot.\n");
                        System.exit(1);
                    }
                }
            }
        } else {
            numOfUsers = AVERAGE_CONCURRENCY;
        }

        buffer.append("<" + PROGRAM_NAME + ",");

        BuggyProgram buggyProgram = new BuggyProgram();
        buggyProgram.go();
        buffer.append(", \n" + pattern + ">\n");

        try {
            outputFile = new FileWriter(outputFilename);

            outputFile.write(buffer.toString());
        } catch (IOException ex) {
            System.out.println("File \"" + outputFilename + "\" is possibly " +
                    "corrupted.\n");
            System.exit(1);
        } catch (NullPointerException ex) {
            System.out.println("File \"" + outputFilename + "\" is possibly " +
                    "corrupted cannot be accessed.\n");
            System.exit(1);
        } catch (Exception ex) {
            System.out.println("File \"" + outputFilename + "\" is possibly " +
                    "corrupted cannot be accessed.\n");
            System.exit(1);
        } finally {
            if (outputFile != null) {
                try {
                    outputFile.close();
                } catch (IOException ex) {
                    System.out.println("Could not close the file \"" + outputFilename +
                            "\".\n");
                }
            }
        }

        et = System.nanoTime();
        tt = (et - st) / 1000;
        System.out.println(tt);

    }


    // ___________________________________________________________________________
    //
    //    Name: acivateUsers
    //      Input:  User array - the users
    //	  Output: None
    //	  Description: Starts the users running.
    // ___________________________________________________________________________

    public void acivateUsers(User[] user) {
        for (int i = 0; i < numOfUsers; ++i) {
            user[i].start();
        }

        for (int i = 0; i < numOfUsers; ++i) {
            try {
                user[i].join();
            } catch (InterruptedException ex) {
                System.out.println("interrupted!!!");
            }
        }
    }


    // ___________________________________________________________________________
    //
    //    Module Name:
    //	  User
    //
    //    Extends:
    //      Thread
    //
    //    Implements:
    //      None
    //
    //    Inner Class Of:
    //      BuggyProgram
    //
    //    Module Description:
    //	  This module includes handling a user in the sample of the buggy
    //      program.
    //
    //      A user may ask to generate a number (unique) for him, to present
    //      it to him, and to record it.
    // ___________________________________________________________________________


    // ============================   Class definition   =========================
    public class User extends Thread {

        // ==============================   Constants   ============================


        // ==============================   Variables   ============================
        int userNumber;
        Random random = new Random(1);

        // ===============================   Methods   =============================

        // _________________________________________________________________________
        //
        //    Name: BuggyProgram (constructor)
        //      Input:  None
        //	    Output: None
        //	    Description: The constructor.
        //                   Initializes the history array, creates users
        //                   (according to NUM_OF_USERS), and starts their running.
        // _________________________________________________________________________

        public User(int userNumber) {
            this.userNumber = userNumber;
        }


        // _________________________________________________________________________
        //
        //    Name: run
        //      Input:  None
        //	    Output: None
        //	    Description: This "starter" method generates a unique random
        //                   number for the user, present the number to screen,
        //                   and records it in the history array.
        // _________________________________________________________________________

        public void run() {

            int i = 0;

            while (i != numOfUsers) {
                generate();

                for (i = 0; i < numOfUsers; ++i) {
                    if (history[i] == randomNumber) {
                        break;
                    }
                }
            }


            present();
            record();


        }


        // _________________________________________________________________________
        //
        //    Name: generate
        //      Input:  None
        //	    Output: None
        //	    Description: This synchronized method generates a random number,
        //                   with the specified maximum number of digits
        //                   (according to MAX_DIGITS).
        // _________________________________________________________________________

        protected synchronized void generate() {
            generated[userNumber] = randomNumber = random.nextInt(1000);
            System.out.println(randomNumber);
//    	  (long) (Math.random(1) *
//                                           Math.pow(10, MAX_DIGITS));
        }


        // _________________________________________________________________________
        //
        //    Name: present
        //      Input:  None
        //	    Output: None
        //	    Description: This synchronized method present the random number,
        //                   which has been generated, on screen.
        // _________________________________________________________________________

        protected synchronized void present() {
            System.out.println("user " + userNumber + " assigned "
                    + (presented[userNumber] = randomNumber) + ".");
        }


        // _________________________________________________________________________
        //
        //    Name: record
        //      Input:  None
        //	    Output: None
        //	    Description: This synchronized method records the random number,
        //                   which has been generated, to the history array.
        // _________________________________________________________________________

        protected synchronized void record() {
            history[userNumber] = randomNumber;
        }
    }
}