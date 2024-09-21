package cerberus;

import static org.junit.Assert.assertTrue;
import org.junit.Test;

public class CalculatorTest {
    @Test
    public void weakTestAdd() {
        // add some dummy calls to other methods, so GZoltar assigns non-zero suspiciousness to those,
        // so ARJA can take those as ingredients
        int foo = Calculator.add(1, 1);
        int bar = Calculator.addThree(1);
        int baz = Calculator.addFive(1);

        int result = Calculator.wrongAdd(1, 1);
        assertTrue(result >= 2);
    }

    @Test
    public void testWithoutAssertion() {
        int result = Calculator.wrongAdd(1, 1);
    }
}