package cerberus;
import cerberus.Calculator;
import org.junit.Test;
import static org.junit.Assert.assertEquals;

public class Test2{

	@Test
	public void test2(){
		int res = Calculator.addThree((-3));
		assertEquals(res, 0);
	}

}