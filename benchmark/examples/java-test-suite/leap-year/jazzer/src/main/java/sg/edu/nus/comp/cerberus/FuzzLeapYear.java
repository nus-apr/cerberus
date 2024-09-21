package sg.edu.nus.comp.cerberus;

import java.util.Iterator;

import com.code_intelligence.jazzer.api.FuzzedDataProvider;
import com.code_intelligence.jazzer.api.FuzzerSecurityIssueHigh;

/**
 * FuzzLeapYear
 */
public class FuzzLeapYear {
    // https://github.com/jhy/jsoup/pull/582
    // "the source of the problem was related to how Jsoup handled tags without a closing > when reaching EOF."

    public static void fuzzerTestOneInput(FuzzedDataProvider data) {
        int a = data.consumeInt();
        assert new LeapYear().LeapChecking(a) == reference(a) : new FuzzerSecurityIssueHigh("Functionality mismatch");
    }

    private static boolean reference(int a){
        boolean leap = false;

        if(year % 4 == 0)
        {
            if( year % 100 == 0)
            {
                if ( year % 400 == 0)
                    leap = true;
                else
                    leap = false;
            }
            else
                leap = true;
        }
        else
            leap = false;

	    return leap;
    }
}
