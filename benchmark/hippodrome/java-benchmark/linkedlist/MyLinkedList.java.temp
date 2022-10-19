package linkedlist;

//MyLinkedList.java
//This class implements a linked list class .

import java.io.IOException;

class MyLinkedList {
    /*Class Member*/
    private MyListNode _header;    //The list head pointer
    private int _maxsize;

    //C'tor
    public MyLinkedList(int n) {
        this._header = new MyListNode(null);
        this._maxsize = n;
    }

    /*Methods*/

    //Checks if list is empty
    public boolean isEmpty() {
        return this._header._next == null;
    }

    //Empties list
    public void clear() {
        this._header._next = null;
    }

    //Returns first element in list
    public MyLinkedListItr first() {
        return new MyLinkedListItr(this._header._next);
    }

    //Inserts element anywhere in list just after current
    public void insert(Object x, MyLinkedListItr p) {
        if (p != null && p._current != null) {
            MyListNode tmp;
            // Delete the synch block for the unsynch case
            synchronized (this) {
                tmp = new MyListNode(x, p._current._next);
            } // Extend the synch block one stmt to eliminate the bug
            p._current._next = tmp;
        }
    }

    //Inserts element to the end of list .
    //If this func is synchronized the bug will not apear
    public void addLast(Object x) {
        MyListNode itr = this._header;
        while (itr._next != null)
            itr = itr._next;
        insert(x, new MyLinkedListItr(itr));
    }

    //Retrieves list size
    public int size() {
        MyListNode itr = this._header;
        int i = 0;

        while (itr._next != null) {
            i++;
            itr = itr._next;
        }

        return i;
    }

    //Finds 'x' element in list
    public MyLinkedListItr find(Object x) {
        MyListNode itr = this._header._next;

        while (itr != null && !itr._element.equals(x))
            itr = itr._next;

        return new MyLinkedListItr(itr);
    }

    //Finds 'x' previous element in list
    public MyLinkedListItr findPrevious(Object x) {
        MyListNode itr = this._header;

        while (itr._next != null && !itr._next._element.equals(x))
            itr = itr._next;

        return new MyLinkedListItr(itr);
    }

    //Removes 'x' element from list
    public void remove(Object x) {
        MyLinkedListItr p = findPrevious(x);

        if (p._current._next != null)
            p._current._next = p._current._next._next;  // Bypass deleted node
    }

    //Prints list
    public void printList(MyLinkedList theList) throws IOException {

        int x;
        if (theList.isEmpty())
            x = 1;
        else {

            MyLinkedListItr itr = theList.first();
            for (; !itr.isPastEnd(); itr.advance())
                x = 1;

        }
        if (this.size() != this._maxsize)
            throw new RuntimeException("bug found");

    }

}
