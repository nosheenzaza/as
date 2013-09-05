package ch.usi.inf.l3.as.plugin

class OrderedLock private(val index: Long) {}

object OrderedLock {
  var lockCount = 0
  def apply() = {
    lockCount += 1
    new OrderedLock(lockCount)
  }
}