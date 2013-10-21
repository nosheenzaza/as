import ch.usi.inf.l3.as.plugin._

object B extends App{
	val v = new MyList(OrderedLock(), 4, OrderedLock())
	println(v.__as_lock)
	println(v.b)
	println(v.lck)
	val v2 = new MyOrderedList(OrderedLock(), 4, OrderedLock())
	println(v2.__as_lock)
	v.doSomething__w_lock(new Node(OrderedLock(), 5), 4)
}