import net.namin.sav.annotation.verify
import net.namin.sav.lib._

// Verified classes. Not yet implemented.
object ex7 {
  @verify
  class BankAccount {
    var balance = 0

    @verify
    def withdraw(amount: Int) {
      precondition(amount >= 0 && balance >= amount)
      val old_balance = old(balance)
      balance -= amount
      postcondition(balance == old_balance - amount && balance >= 0)
    }

    @verify
    def deposit(amount: Int) {
      precondition(amount >= 0 && balance >= 0)
      val old_balance = old(balance)
      balance += amount
      postcondition(balance == old_balance + amount && balance >= 0)
    }
  }

  @verify
  def transfer(a: BankAccount, b: BankAccount, amount: Int) {
    precondition(amount >= 0 && a.balance >= amount && b.balance >= 0)
    val old_a_balance = old(a.balance)
    val old_b_balance = old(b.balance)
    a.withdraw(amount)
    b.deposit(amount)
    postcondition(a.balance + b.balance == old_a_balance + old_b_balance && a.balance >= 0 && b.balance >= 0)
  }
}
