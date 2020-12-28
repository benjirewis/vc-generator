import scala.util.parsing.combinator._
import java.io._
import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.Map
import sys.process._


object VCGen {

  /* Arithmetic expressions. */
  trait ArithExp

  case class Num(value: Int) extends ArithExp
  case class Var(name: String) extends ArithExp
  case class Read(name: String, ind: ArithExp) extends ArithExp
  case class WriteExp(name: String, ind: ArithExp, value: ArithExp) extends ArithExp
  case class Add(left: ArithExp, right: ArithExp) extends ArithExp
  case class Sub(left: ArithExp, right: ArithExp) extends ArithExp
  case class Mul(left: ArithExp, right: ArithExp) extends ArithExp
  case class Div(left: ArithExp, right: ArithExp) extends ArithExp
  case class Mod(left: ArithExp, right: ArithExp) extends ArithExp
  case class Parens(a: ArithExp) extends ArithExp


  /* Comparisons of arithmetic expressions. */
  type Comparison = Product3[ArithExp, String, ArithExp]


  /* Boolean expressions. */
  trait BoolExp

  case class BComparison(cmp: Comparison) extends BoolExp
  case class BNot(b: BoolExp) extends BoolExp
  case class BDisj(left: BoolExp, right: BoolExp) extends BoolExp
  case class BConj(left: BoolExp, right: BoolExp) extends BoolExp
  case class BParens(b: BoolExp) extends BoolExp


  /* Statements and blocks. */
  trait Statement
  type Block = List[Statement]

  case class Assign(x: String, value: ArithExp) extends Statement
  case class Write(x: String, ind: ArithExp, value: ArithExp) extends Statement
  case class ParAssign(x1: String, x2: String, value1: ArithExp, value2: ArithExp) extends Statement
  case class If(cond: BoolExp, th: Block, el: Block) extends Statement
  case class While(cond: BoolExp, inv: List[Assertion], body: Block) extends Statement


  /* Logical assertions. */
  trait Assertion
  type Preconditions = List[Assertion]
  type Postconditions = List[Assertion]

  case class AssertNot(x: Assertion) extends Assertion
  case class AssertComp(x: Comparison) extends Assertion
  case class AssertDisj(left: Assertion, right: Assertion) extends Assertion
  case class AssertConj(left: Assertion, right: Assertion) extends Assertion
  case class AssertImp(left: Assertion, right: Assertion) extends Assertion
  case class AssertForAll(x: List[String], y: Assertion) extends Assertion
  case class AssertExists(x: List[String], y: Assertion) extends Assertion
  case class AssertParens(x: Assertion) extends Assertion


  /* Guarded commands. */
  trait GuardedCommand

  case class Assume(x: Assertion) extends GuardedCommand // assume(x)
  case class BoolAssume(x: BoolExp) extends GuardedCommand // assume(bool)
  case class Assert(x: Assertion) extends GuardedCommand // assert(x)
  case class Havoc(x: String) extends GuardedCommand // havoc(x)
  case class AHavoc(x: String) extends GuardedCommand // havoc(x) where x is an array
  case class Sequence(x: GuardedCommand, y: GuardedCommand) extends GuardedCommand // x ; y
  case class Box(x: GuardedCommand, y: GuardedCommand) extends GuardedCommand // x [] y


  /* Complete programs. */
  type Program = Product4[String, Preconditions, Postconditions, Block]


  object ImpParser extends RegexParsers {
    /* General helpers. */
    def pvar  : Parser[String] = "\\p{Alpha}(\\p{Alnum}|_)*".r

    /* Parsing for ArithExp. */
    def num   : Parser[ArithExp] = "-?\\d+".r ^^ (s => Num(s.toInt))
    def atom  : Parser[ArithExp] =
      "(" ~> aexp <~ ")" |
      pvar ~ ("[" ~> aexp <~ "]") ^^ {case v ~ i => Read(v, i)} |
      num | pvar ^^ { Var(_) } |
      "-" ~> atom ^^ { Sub(Num(0), _) }
    def factor: Parser[ArithExp] =
      atom ~ rep("*" ~ atom | "/" ~ atom | "%" ~ atom) ^^ {
        case left ~ list => (left /: list) {
          case (left, "*" ~ right) => Mul(left, right)
          case (left, "/" ~ right) => Div(left, right)
          case (left, "%" ~ right) => Mod(left, right)
        }
      }
    def term  : Parser[ArithExp] =
      factor ~ rep("+" ~ factor | "-" ~ factor) ^^ {
        case left ~ list => (left /: list) {
          case (left, "+" ~ right) => Add(left, right)
          case (left, "-" ~ right) => Sub(left, right)
        }
      }
    def aexp  : Parser[ArithExp] = term

    /* Parsing for Comparison. */
    def comp  : Parser[Comparison] =
      aexp ~ ("=" | "<=" | ">=" | "<" | ">" | "!=") ~ aexp ^^ {
        case left ~ op ~ right => (left, op, right)
      }

    /* Parsing for BoolExp. */
    def batom : Parser[BoolExp] =
      "(" ~> bexp <~ ")" | comp ^^ { BComparison(_) } | "!" ~> batom ^^ { BNot(_) }
    def bconj : Parser[BoolExp] =
      batom ~ rep("&&" ~> batom) ^^ {
        case left ~ list => (left /: list) { BConj(_, _) }
      }
    def bdisj : Parser[BoolExp] =
      bconj ~ rep("||" ~> bconj) ^^ {
        case left ~ list => (left /: list) { BDisj(_, _) }
      }
    def bexp  : Parser[BoolExp] = bdisj

    /* Parsing for Statement and Block. */
    def block : Parser[Block] = rep(stmt)
    def stmt  : Parser[Statement] =
      pvar ~ ("[" ~> aexp <~ "]") ~ (":=" ~> aexp <~ ";") ^^ {
        case v ~ i ~ e => Write(v, i, e)
      } |
      (pvar <~ ":=") ~ (aexp <~ ";") ^^ {
        case v ~ e => Assign(v, e)
      } |
      (pvar <~ ",") ~ (pvar <~ ":=") ~ (aexp <~ ",") ~ (aexp <~ ";") ^^ {
        case v1 ~ v2 ~ e1 ~ e2 => ParAssign(v1, v2, e1, e2)
      } |
      ("if" ~> bexp <~ "then") ~ (block <~ "else") ~ (block <~ "end") ^^ {
        case c ~ t ~ e => If(c, t, e)
      } |
      ("if" ~> bexp <~ "then") ~ (block <~ "end") ^^ {
        case c ~ t => If(c, t, Nil)
      } |
      ("while" ~> (bexp ~ rep("inv" ~> assn)) <~ "do") ~ (block <~ "end") ^^ {
        case c ~ list ~ b => While(c, list, b)
      }

    /* Parsing for Assertions. */
    def aatom: Parser[Assertion] =
      "(" ~> assn <~ ")" | comp ^^ {
        AssertComp(_)
      } |
      "!" ~> aatom ^^ {
        AssertNot(_)
      } |
      ("forall" ~> rep(pvar)) ~ ("," ~> assn) ^^ {
        case x ~ a => AssertForAll(x, a)
      } |
      ("exists" ~> rep(pvar)) ~ ("," ~> assn) ^^ {
        case x ~ a => AssertExists(x, a)
      }
    def aconj : Parser[Assertion] =
      aatom ~ rep("&&" ~> aatom) ^^ {
        case left ~ list => (left /: list) { AssertConj(_, _) }
      }
    def adisj : Parser[Assertion] =
      aconj ~ rep("||" ~> aconj) ^^ {
        case left ~ list => (left /: list) { AssertDisj(_, _) }
      }
    def aimpl : Parser[Assertion] =
      adisj ~ rep("==>" ~> adisj) ^^ {
        case left ~ list => (left /: list) { AssertImp(_, _) }
      } |
      adisj
    def assn : Parser[Assertion] = aimpl

    /* Parsing for Program. */
    def prog   : Parser[Program] =
      ("program" ~> (pvar ~ rep("pre" ~> assn) ~ rep("post" ~> assn)) <~ "is") ~ (block <~ "end") ^^ {
        case n ~ pre ~ post ~ b => (n, pre, post, b)
      }
  }

  /* Combine two guarded commands into one Sequence. */
  def concat(gc: GuardedCommand, gc2: GuardedCommand): GuardedCommand = {
    var ret : GuardedCommand = null
    if (gc == null) {
      ret = gc2
    }
    else if (gc2 == null) {
      ret = gc
    }
    else {
      ret = Sequence(gc, gc2)
    }
    return ret
  }

  /* Havoc all vars in the given block as a guarded command. */
  def havoc(stmt: Block): GuardedCommand = {
    var ret : GuardedCommand = null

    for (line <- stmt) {
      line match {
        case Assign(x, value) => ret = concat(ret, Havoc(x))
        case Write(x, ind, value) => ret = concat(ret, AHavoc(x))
        case ParAssign(x1, x2, value1, value2) => ret = concat(ret,
          concat(Havoc(x1), Havoc(x2)))
        case If(cond, th, el) => ret = concat(ret, concat(havoc(th), havoc(el)))
        case While(cond, inv, body) => ret = concat(ret, havoc(body))
        case _ => ret = concat(ret, null)
      }
    }

    return ret
  }

  /* Amend an assertion with fresh variables. */
  def freshenAssertion(a: Assertion, s: String, tmp: String): Assertion = {
    a match {
      case AssertNot(x) => return AssertNot(freshenAssertion(x, s, tmp))
      case AssertComp(x) => return AssertComp((freshenStatement(x._1, s, tmp), x._2,
        freshenStatement(x._3, s, tmp)))
      case AssertDisj(left, right) => return AssertDisj(freshenAssertion(left, s, tmp),
        freshenAssertion(right, s, tmp))
      case AssertConj(left, right) => return AssertConj(freshenAssertion(left, s, tmp),
        freshenAssertion(right, s, tmp))
      case AssertImp(left, right) => return AssertImp(freshenAssertion(left, s, tmp),
        freshenAssertion(right, s, tmp))
      case AssertForAll(x, y) => {
        var (freshAssert, freshList) = (y, List[String]())
        for (item <- x) {
          var freshItem = item
          if (!item.endsWith("uni")) { // add "uni" suffix to all vars in forall list.
            freshItem = item + "uni"
            freshAssert = freshenAssertion(y, item, freshItem)
          }
          freshList ::= freshItem
        }
        freshList = freshList.distinct
        return AssertForAll(freshList, freshenAssertion(freshAssert, s, tmp))
      }
      case AssertExists(x, y) => return AssertExists(x, freshenAssertion(y, s, tmp))
      case AssertParens(x) => return AssertParens(freshenAssertion(x, s, tmp))
      case _ => return null
    }
  }

  /* Amend a statement with fresh variables. */
  def freshenStatement(stmt: ArithExp, x: String, tmp: String): ArithExp = {
    stmt match {
      case Num(value) => return Num(value)
      case Var(name) => {
        // if variable of matching name, replace with tmp.
        if (name == x) {
          return Var(tmp)
        }
        else {
          return Var(name)
        }
      }
      case Read(name, ind) => {
        // if read of matching array name, replace with tmp.
        if (name == x) {
          return Read(tmp, freshenStatement(ind, x, tmp))
        }
        else {
          return Read(name, freshenStatement(ind, x, tmp))
        }
      }
      case WriteExp(name, ind, value) => {
        // if write of matching array name, replace with tmp.
        if (name == x) {
          return WriteExp(tmp, freshenStatement(ind, x, tmp), freshenStatement(value, x, tmp))
        }
        else {
          return WriteExp(name, freshenStatement(ind, x, tmp), freshenStatement(value, x, tmp))
        }
      }
      case Add(left, right) => return Add(freshenStatement(left, x, tmp),
        freshenStatement(right, x, tmp))
      case Sub(left, right) => return Sub(freshenStatement(left, x, tmp),
        freshenStatement(right, x, tmp))
      case Mul(left, right) => return Mul(freshenStatement(left, x, tmp),
        freshenStatement(right, x, tmp))
      case Div(left, right) => return Div(freshenStatement(left, x, tmp),
        freshenStatement(right, x, tmp))
      case Mod(left, right) => return Mod(freshenStatement(left, x, tmp),
        freshenStatement(right, x, tmp))
      case Parens(a) => return Parens(freshenStatement(a, x, tmp))
      case _ => return null
    }
  }

  /* Find guarded command of a list of assumptions. */
  def assumeToGC(stmt: List[Assertion]): GuardedCommand = {
    var ret : GuardedCommand = null

    // assume each assumption in the list.
    for (a <- stmt) {
      ret = concat(ret, Assume(a))
    }

    return ret
  }

  /* Find guarded command of a list of assertions. */
  def assertToGC(stmt: List[Assertion]): GuardedCommand = {
    var ret : GuardedCommand = null

    // assert each assertion in the list.
    for (a <- stmt) {
      ret = concat(ret, Assert(a))
    }

    return ret
  }

  /* Find guarded command of an Assign statement. */
  def assignToGC(stmt: Assign, vars: Map[String, Int]): (GuardedCommand, Map[String, Int]) = {
    var (x, value) = (stmt.x, stmt.value)

    var new_vars = vars.updated(x, vars.get(x).getOrElse(0) + 1)
    var tmp = x + "temp" + new_vars(x) // create temp variable with name of var + temp + number of temp.

    return (concat(Assume(AssertComp((Var(tmp), "=", Var(x)))),
      concat(Havoc(x), Assume(AssertComp((Var(x), "=", freshenStatement(value, x, tmp)))))), new_vars)
  }

  /* Find guarded command of a Write statement. */
  def writeToGC(stmt: Write, vars: Map[String, Int]): (GuardedCommand, Map[String, Int]) = {
    var (x, ind, value) = (stmt.x, stmt.ind, stmt.value)

    var new_vars = vars.updated(x, vars.get(x).getOrElse(0) + 1)
    var tmp = x + "temp" + new_vars(x) // create temp variable with name of var + temp + number of temp.

    return (concat(Assume(AssertComp((Var(tmp), "=", Var(x)))),
      concat(AHavoc(x), Assume(AssertComp((Var(x), "=",
        WriteExp(tmp, freshenStatement(ind, x, tmp), freshenStatement(value, x, tmp))))))), new_vars)
  }

  /* Find guarded command of a ParAssign statement. */
  def parAssignToGC(stmt: ParAssign, vars: Map[String, Int]): (GuardedCommand, Map[String, Int]) = {
    var (x1, x2, value1, value2) = (stmt.x1, stmt.x2, stmt.value1, stmt.value2)

    // update vars for both x1 and x2.
    var new_vars = vars.updated(x1, vars.get(x1).getOrElse(0) + 1)
    new_vars = new_vars.updated(x2, vars.get(x2).getOrElse(0) + 1)
    // create new temp variables with name of vars + temp + number of temps.
    var (tmp, tmp2) = (x1 + "temp" + new_vars(x1), x2 + "temp" + new_vars(x2))

    // assume tmp1 = x1; assume tmp2 = x2; havoc x1; havoc x2;
    var gc: GuardedCommand = concat(Assume(AssertComp((Var(tmp), "=", Var(x1)))),
      concat(Assume(AssertComp((Var(tmp2), "=", Var(x2)))),
        concat(Havoc(x1), Havoc(x2))))

    // assume x1 = value1[tmp/x1, tmp2/x2]; assume x2 = value2[tmp/x1, tmp2/x2];
    var gc2: GuardedCommand = concat(Assume(AssertComp((Var(x1), "=",
      freshenStatement(freshenStatement(value1, x2, tmp2), x1, tmp)))),
        Assume(AssertComp((Var(x2), "=",
          freshenStatement(freshenStatement(value2, x1, tmp), x2, tmp2)))))

    return (concat(gc, gc2), new_vars)
  }

  /* Find guarded command of an If statement. */
  def ifToGC(stmt: If, vars: Map[String, Int]): (GuardedCommand, Map[String, Int]) = {
    var (cond, th, el) = (stmt.cond, stmt.th, stmt.el)

    // run then and else branches.
    var th_command = programToGCH(th, vars)
    var el_command = programToGCH(el, th_command._2)

    // create x [] y;
    var non_deter = Box(concat(BoolAssume(cond), th_command._1),
      concat(BoolAssume(BNot(cond)), el_command._1))

    return (non_deter, el_command._2)
  }

  /* Find guarded command of a While statement. */
  def whileToGC(stmt: While, vars: Map[String, Int]): (GuardedCommand, Map[String, Int]) = {
    var (cond, inv, body) = (stmt.cond, stmt.inv, stmt.body)

    // define havocs of entire body + assertions/assumptions of invariant.
    var (new_body, asserts, assumes) = (havoc(body), assertToGC(inv), assumeToGC(inv))

    var command = programToGCH(body, vars)

    // (assert inv; assume false) [] assume !b;
    // note: Asserted 1 < 0 to represent "false".
    var gc: GuardedCommand = concat(asserts, concat(new_body, concat(assumes,
      Box(concat(BoolAssume(cond), concat(command._1,
        concat(asserts, Assume(AssertComp((Num(1), "<", Num(0))))))),
          BoolAssume(BNot(cond))))))

    return (gc, command._2)
  }

  /* programToGC helper for internal calls (adds ability to pass in vars map). */
 def programToGCH(program: Block, vars: Map[String, Int]): (GuardedCommand, Map[String, Int]) = {
    var ret : GuardedCommand = null

    // create ret_vars based on passed in variables.
    var ret_vars = vars match {
      case null => Map[String, Int]()
      case _ => vars
    }

    for (line <- program) {
      line match {
        case Assign(x, value) => {
          var command = assignToGC(Assign(x, value), ret_vars)
          ret = concat(ret, command._1)
          ret_vars = command._2
        }
        case Write(x, ind, value) => {
          var command = writeToGC(Write(x, ind, value), ret_vars)
          ret = concat(ret, command._1)
          ret_vars = command._2
        }
        case ParAssign(x1, x2, value1, value2) => {
          var command = parAssignToGC(ParAssign(x1, x2, value1, value2), ret_vars)
          ret = concat(ret, command._1)
          ret_vars = command._2
        }
        case If(cond, th, el) => {
          var command = ifToGC(If(cond, th, el), ret_vars)
          ret = concat(ret, command._1)
          ret_vars = command._2
        }
        case While(cond, inv, body) => {
          var command = whileToGC(While(cond, inv, body), ret_vars)
          ret = concat(ret, command._1)
          ret_vars = command._2
        }
        case _ => ret = concat(ret, null)
      }
    }

    return (ret, ret_vars)
 }

  /* Find guarded commands of a program. */
  def programToGC(pre: Preconditions, post: Postconditions, program: Block): GuardedCommand = {
    var ret : GuardedCommand = null
    var vars = Map[String, Int]()

    for (line <- program) {
      line match {
        case Assign(x, value) => {
          var command = assignToGC(Assign(x, value), vars)
          ret = concat(ret, command._1)
          vars = command._2
        }
        case Write(x, ind, value) => {
          var command = writeToGC(Write(x, ind, value), vars)
          ret = concat(ret, command._1)
          vars = command._2
        }
        case ParAssign(x1, x2, value1, value2) => {
          var command = parAssignToGC(ParAssign(x1, x2, value1, value2), vars)
          ret = concat(ret, command._1)
          vars = command._2
        }
        case If(cond, th, el) => {
          var command = ifToGC(If(cond, th, el), vars)
          ret = concat(ret, command._1)
          vars = command._2
        }
        case While(cond, inv, body) => {
          var command = whileToGC(While(cond, inv, body), vars)
          ret = concat(ret, command._1)
          vars = command._2
        }
        case _ => ret = concat(ret, null)
      }
    }

    return concat(assumeToGC(pre), concat(ret, assertToGC(post)))
  }

  /* Turn any bool expression into a full assertion. */
  def boolHandler(b: BoolExp): Assertion = {
    b match {
      case BComparison(cmp) => return AssertComp(cmp._1, cmp._2, cmp._3)
      case BNot(b) => return AssertNot(boolHandler(b))
      case BDisj(left, right) => return AssertDisj(boolHandler(left), boolHandler(right))
      case BConj(left, right) => return AssertConj(boolHandler(left), boolHandler(right))
      case BParens(b) => return AssertParens(boolHandler(b))
    }
  }

  /* Find verification condition of one guarded command. */
  def gcToVc(gc: GuardedCommand, a: Assertion, vars: Map[String, Int], arrs: Map[String, Int]):
    (Assertion, Map[String, Int], Map[String, Int]) = {
    gc match {
      case Assume(x) => return (AssertImp(x, a), vars, arrs)
      case BoolAssume(x) => return (AssertImp(boolHandler(x), a), vars, arrs) // run through boolHandler.
      case Assert(x) => return (AssertConj(x, a), vars, arrs)
      case Havoc(x) => {
        var new_vars = vars.updated(x, vars.get(x).getOrElse(0) + 1)
        return (freshenAssertion(a, x, x + "new" + new_vars(x)), new_vars, arrs)
      }
      case AHavoc(x) => {
        var new_arrs = arrs.updated(x, arrs.get(x).getOrElse(0) + 1)
        var new_name = x + "new" + new_arrs(x)
        new_arrs = new_arrs.updated(new_name, new_arrs.get(new_name).getOrElse(0) + 1)
        return (freshenAssertion(a, x, new_name), vars, new_arrs)
      }
      case Sequence(x, y) => {
        // find VC of second command first.
        var vc2 = gcToVc(y, a, vars, arrs)
        return gcToVc(x, vc2._1, vc2._2, vc2._3)
      }
      case Box(x, y) => {
        var vc = gcToVc(x, a, vars, arrs)
        var vc2 = gcToVc(y, a, vc._2, vc._3)
        return (AssertConj(vc._1, vc2._1), vc2._2, vc2._3)
      }
      case _ => return (null, vars, arrs)
    }
  }

  /* Translate ae (an ArithExp) to SMT format. */
  def aeToSMT(ae: ArithExp, vars: ArrayBuffer[String], arrs: ArrayBuffer[String]):
    (String, ArrayBuffer[String], ArrayBuffer[String]) = {
      ae match {
        case Num(value) => return (value.toString, vars, arrs)
        case Var(name) => {
          vars += name // add name of variable to vars map.
          return (name, vars.distinct, arrs)
        }
        case Read(name, ind) => {
          var indAE = aeToSMT(ind, vars, arrs)
          arrs += name
          return ("(select " + name + " " + indAE._1 + ")", indAE._2, arrs)
        }
        case WriteExp(name, ind, value) => {
          var valueAE = aeToSMT(value, vars, arrs)
          var indAE = aeToSMT(ind, valueAE._2, valueAE._3)
          arrs += name
          return ("(store " + name + " " + indAE._1 + " " + valueAE._1 + ")", indAE._2, arrs)
        }
        case Add(left, right) => {
          var valueAE = aeToSMT(left, vars, arrs)
          var value2AE = aeToSMT(right, valueAE._2, valueAE._3)
          return ("(+ " + valueAE._1 + " " + value2AE._1 + ")", value2AE._2, value2AE._3)
        }
        case Sub(left, right) => {
          var valueAE = aeToSMT(left, vars, arrs)
          var value2AE = aeToSMT(right, valueAE._2, valueAE._3)
          return ("(- " + valueAE._1 + " " + value2AE._1 + ")", value2AE._2, value2AE._3)
        }
        case Mul(left, right) => {
          var valueAE = aeToSMT(left, vars, arrs)
          var value2AE = aeToSMT(right, valueAE._2, valueAE._3)
          return ("(* " + valueAE._1 + " " + value2AE._1 + ")", value2AE._2, value2AE._3)
        }
        case Div(left, right) => {
          var valueAE = aeToSMT(left, vars, arrs)
          var value2AE = aeToSMT(right, valueAE._2, valueAE._3)
          return ("(div " + valueAE._1 + " " + value2AE._1 + ")", value2AE._2, value2AE._3)
        }
        case Mod(left, right) => {
          var valueAE = aeToSMT(left, vars, arrs)
          var value2AE = aeToSMT(right, valueAE._2, valueAE._3)
          return ("(mod " + valueAE._1 + " " + value2AE._1 + ")", value2AE._2, value2AE._3)
        }
        case Parens(a) => return aeToSMT(a, vars, arrs)
        case _ => ("", vars, arrs)
      }
  }

  /* Translate stmt (an Assertion) to SMT format. */
  def vcToSMT(stmt: Assertion, vars: ArrayBuffer[String], arrs: ArrayBuffer[String]):
    (String, ArrayBuffer[String], ArrayBuffer[String]) = {
    stmt match {
      case AssertNot(x) => {
        var assertNot = vcToSMT(x, vars, arrs)
        return ("(not" + assertNot._1 + ")", assertNot._2, assertNot._3)
      }
      case AssertComp(x) => {
        var assertCompLeft = aeToSMT(x._1, vars, arrs)
        var assertCompRight = aeToSMT(x._3, assertCompLeft._2, assertCompLeft._3)
        x._2 match {
          case "!=" => return ("(not (= " + assertCompLeft._1 + " " + assertCompRight._1 + "))",
            assertCompRight._2, assertCompRight._3)
          case _ => return ("(" + x._2 + " " + assertCompLeft._1 + " " + assertCompRight._1
            + ")", assertCompRight._2, assertCompRight._3)
        }
      }
      case AssertDisj(left, right) => {
        var assertLeft = vcToSMT(left, vars, arrs)
        var assertRight = vcToSMT(right, assertLeft._2, assertLeft._3)
        return ("(or " + assertLeft._1 + assertRight._1 + ")", assertRight._2, assertRight._3)
      }
      case AssertConj(left, right) => {
        var assertLeft = vcToSMT(left, vars, arrs)
        var assertRight = vcToSMT(right, assertLeft._2, assertLeft._3)
        return ("(and " + assertLeft._1 + assertRight._1 + ")", assertRight._2, assertRight._3)
      }
      case AssertImp(left, right) => {
        var assertLeft = vcToSMT(left, vars, arrs)
        var assertRight = vcToSMT(right, assertLeft._2, assertLeft._3)
        return ("(=> " + assertLeft._1 + assertRight._1 + ")", assertRight._2, assertRight._3)
      }
      case AssertForAll(x, y) => {
        var (assertion, uni) = (vcToSMT(y, vars, arrs), "")
        for (item <- x) {
          uni += "(" + item + " Int) "
        }
        return ("(forall (" + uni + ")" + assertion._1 + ")", assertion._2, assertion._3)
      }
      case AssertExists(x, y) => {
        var (assertion, ex) = (vcToSMT(y, vars, arrs), "")
        for (item <- x) {
          ex += "(" + item + " Int) "
        }
        return ("(exists (" + ex + ")" + assertion._1 + ")", assertion._2, assertion._3)
      }
      case AssertParens(x) => return vcToSMT(x, vars, arrs)
      case _ => return null
    }
  }

  /* Write vc (a verification condition) to file "smt_input.txt" in correct SMT format. */
  def writeToSMT(vc: Assertion, passed_arrs: Map[String, Int]): Unit = {
    var (vars, arrs) = (ArrayBuffer[String](), ArrayBuffer[String]())
    var smt = vcToSMT(vc, vars, arrs)

    var (smt_body, print_vars, print_arrs) = ("true", ArrayBuffer[String](), ArrayBuffer[String]())
    if (smt != null) {
      smt_body = smt._1
      print_vars = smt._2
      print_arrs = smt._3
    }

    // add arrays in passed_arrs to print_arrs.
    for (arr <- passed_arrs) {
      print_arrs += arr._1
    }

    // remove all arrays from print_vars to avoid duplicates between.
    for (print_arr <- print_arrs) {
      if (print_vars contains print_arr) {
        print_vars -= print_arr
      }
    }

    // remove duplicates from both printing arrays.
    print_vars = print_vars.distinct
    print_arrs = print_arrs.distinct

    // write variables in correct format.
    var var_lines : String = ""

    for (item <- print_vars) {
      // declare a function of arity 0 for each variable.
      var_lines += "(declare-fun " + item + " () Int)\n"
    }

    // write arrays in correct format.
    var arr_lines : String = ""

    for (arr <- print_arrs) {
      // declare an array for each array in arrs.
      arr_lines += "(declare-fun " + arr + " () (Array Int Int))\n"
    }

    // create full smt_formatted string.
    // note that the body is surrounded by a not, so "unsat" from z3 means verified, and
    // "sat" means not verified.
    var smt_formatted = var_lines + arr_lines + "(assert (not " + smt_body + "))\n(check-sat)"

    // create new file "smt_input.txt" in currdir and write SMT format to it.
    var smt_input = new File("smt_input.txt")
    var writer = new BufferedWriter(new FileWriter(smt_input))
    writer.write(smt_formatted)
    writer.close()
  }

  def main(args: Array[String]): Unit = {
    val reader = new FileReader(args(0))
    import ImpParser._;

    // parse given program file.
    var parse = parseAll(prog, reader)
    var (pre, post, block) = (parse.get._2, parse.get._3, parse.get._4)

    // compute guarded commands from program
    var gc = programToGC(pre, post, block)

    // define vars and arrs maps.
    var (vars, arrs) = (Map[String, Int](), Map[String, Int]())

    // generate verification conditions from guarded commands (0 < 1 stands for "true").
    var vc = gcToVc(gc, AssertComp((Num(0), "<", Num(1))), vars, arrs)

    // write verification conditions to SMT format in "smt_input.txt"
    writeToSMT(vc._1, vc._3)

    // use Z3 theorem solver on "smt_input.txt" file.
    var process = Process("z3 smt_input.txt")
    for (line <- process.lineStream) {
      // because body was surrounded by "not", "unsat" means verified.
      if (line == "unsat\n" || line == "unsat") {
        println("Verified")
        return
      }
    }

    // otherwise: unsatisfiable
    println("Not verified")
  }
}
