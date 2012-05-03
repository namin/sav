import net.namin.sav.annotation.verify

object ok7a {
  @verify
  def withdraw(initBalance:Int, amount: Int) {
    var balance: Int = initBalance
    assume(amount >= 0 && balance >= amount)
    val old_balance: Int = balance
    balance = balance - amount
    assert(balance == old_balance - amount && balance >= 0)
  }
}
