package cerberus;
import cerberus.Calculator;
import org.junit.Test;
import static org.junit.Assert.assertEquals;

public class Test3{

	@Test
	public void test3(){
		int res = Calculator.addThree((5));
		assertEquals(res, 8);
	}

}