import ch.usi.inf.l3.ascala._
import ch.usi.inf.l3.as.plugin.OrderedLock

//object Main extends App {

//  class MyList(val cp: Int) extends MySeq("my_seq") {
//    val lck: Object = new Object()
//    val x: atomic = null
//    @atomic('a) var list_f1 = "f1 list"
//    @atomic('a2) var list_f2 = "f2 list"
//    class Node {
//      @atomic('b) var node_f1 = "here"
//    }
//
//    def obj_param() = {
//      1
//    }
//    
//    def foo(@atomic('a) p: Int) = {
//      lck.synchronized {
//        @atomic('broken) val x = 1
//        val x2 = 2
//        
//    }
//    }
//
//    def foo2() = {
//      lck.synchronized {
//        val x = 1
//        val x2 = 2
//      }
//
//    }
//  }

//  println("Welcome to Atomic Scala!")

//  class MySeq(@atomic('sps) var cp_1: String) {
//    // @atomic('ss) var seq_f1 = "field in parent"
//  }
//  val lst = new MyList(3)
//  val lock = OrderedLock()
//}

class MyList(val b: Int = 10) {
  @atomic('a) var list_f1 = "f1 list"
}


