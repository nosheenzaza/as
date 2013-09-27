import ch.usi.inf.l3.as.plugin._

object B extends App{
	val v = new MyList(OrderedLock(), 4, OrderedLock())
	println(v.__as_lock)
	println(v.b)
	println(v.lck)
	v.doSomething__w_lock(new Node(OrderedLock(), 5), 4)
}