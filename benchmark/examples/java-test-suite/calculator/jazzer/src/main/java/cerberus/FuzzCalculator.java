package cerberus;

import java.util.Iterator;

import com.code_intelligence.jazzer.api.FuzzedDataProvider;
import com.code_intelligence.jazzer.api.FuzzerSecurityIssueHigh;

/**
 * FuzzCalculator
 */
public class FuzzCalculator {
    public static void fuzzerTestOneInput(FuzzedDataProvider data) {
        int a =data.consumeInt(), b = data.consumeInt();
        assert Calculator.wrongAdd(a,b) == a+b : new FuzzerSecurityIssueHigh("Functionality mismatch");
    }
}
