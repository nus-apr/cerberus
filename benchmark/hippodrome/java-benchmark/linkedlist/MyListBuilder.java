package linkedlist;

//MyListBuilder.java
//This class builds a shared list from given threads .

import java.io.IOException;

class MyListBuilder implements Runnable
{
	/*Class Members*/
	public boolean _debug = true;
	public Object _list = null;
	public int _bound1 = 0;
	public int _bound2 = 0;

	//C'tor
	public MyListBuilder(Object lst,int bnd1,int bnd2,boolean dbg)
	{
		this._debug = dbg;

			this._list = (MyLinkedList)lst;

		this._bound1 = bnd1;
		this._bound2 = bnd2;
	}

	/*Methods*/

	//The processor
	public void run()
	{
		for ( int i = this._bound1; i < this._bound2 ;i++ )
		{
				((MyLinkedList)_list).addLast(new Integer(i));
		}
	}

	//Prints list elements
	public void print()
	{
		int size;
		int x;

			size = ((MyLinkedList)_list).size();

		try
		{

				((MyLinkedList)this._list).printList((MyLinkedList)_list);

		}
		catch(IOException e)
		{
		}

	}


	//Empties list
	public void empty()
	{
			((MyLinkedList)_list).clear();
	}

}

