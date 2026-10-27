module procurement {
  // Repair round 3: enable refunds for expired, unconfirmed orders.
  // One buyer, one seller, one order, one unit of escrowed money.
  var s: {
    funded: bool, shipped: bool, confirmed: bool, expired: bool,
    buyer: int, escrow: int, seller: int, payments: int
  }

  action init = s' = {
    funded: false, shipped: false, confirmed: false, expired: false,
    buyer: 1, escrow: 0, seller: 0, payments: 0
  }

  action deposit = all {
    not(s.funded),
    s' = { ...s, funded: true, buyer: 0, escrow: 1 }
  }

  action ship = all {
    s.escrow == 1, not(s.expired), not(s.shipped),
    s' = { ...s, shipped: true }
  }

  action confirm = all {
    s.escrow == 1, s.shipped, not(s.expired), not(s.confirmed),
    s' = { ...s, confirmed: true }
  }

  action expire = all {
    s.escrow == 1, not(s.expired),
    s' = { ...s, expired: true }
  }

  action pay = all {
    s.confirmed, s.escrow == 1, s.payments == 0,
    s' = { ...s, escrow: s.escrow - 1,
      seller: s.seller + 1, payments: s.payments + 1 }
  }

  action refund = all {
    s.expired, not(s.confirmed), s.escrow == 1,
    s' = { ...s, escrow: 0, buyer: s.buyer + 1 }
  }

  action idle = s' = s
  action step = any { deposit, ship, confirm, expire, pay, refund, idle }

  // CHECKS: this block must remain identical across every version.
  val noPaymentWithoutConfirmation = s.payments > 0 implies s.confirmed
  val noDoublePayment = s.payments <= 1
  val moneyConserved = and {
    s.buyer >= 0, s.escrow >= 0, s.seller >= 0,
    s.buyer + s.escrow + s.seller == 1
  }
  temporal systemFairness = and {
    weakFair(expire, s), weakFair(pay, s), weakFair(refund, s)
  }
  temporal noLockedFunds = systemFairness implies
    always(s.escrow > 0 implies eventually(s.escrow == 0))

  // Negated reachability witnesses: a counterexample is success here.
  val neverPaid = not(s.confirmed and s.payments == 1 and s.escrow == 0)
  val neverRefunded = not(s.funded and s.expired and s.buyer == 1 and s.escrow == 0)
}
