package cerberus;
import cerberus.Calculator;
import org.junit.Test;
import static org.junit.Assert.assertEquals;

public class Test1{

	@Test
	public void test1(){
		int res = Calculator.wrongAdd(10, -1);
		assertEquals(res, 9);
	}

}