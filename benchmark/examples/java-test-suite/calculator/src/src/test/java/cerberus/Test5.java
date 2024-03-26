package cerberus;
import cerberus.Calculator;
import org.junit.Test;
import static org.junit.Assert.assertEquals;

public class Test5{

	@Test
	public void test5(){
		int res = Calculator.addFive((5));
		assertEquals(res, 10);
	}

}