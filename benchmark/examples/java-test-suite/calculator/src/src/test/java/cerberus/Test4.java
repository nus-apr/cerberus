package cerberus;
import cerberus.Calculator;
import org.junit.Test;
import static org.junit.Assert.assertEquals;

public class Test4{

	@Test
	public void test4(){
		int res = Calculator.addFive((-5));
		assertEquals(res, 0);
	}

}