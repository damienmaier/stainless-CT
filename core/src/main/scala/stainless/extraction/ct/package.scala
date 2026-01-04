package stainless
package extraction
package ct

import inox.Context

class Instrumentation(override val s: xlang.trees.type, override val t: xlang.trees.type)
                     (using override val context: inox.Context)
    extends oo.IdentityTypeDefs
        with oo.IdentityClasses
        with IdentitySorts
        with IdentityFunctions
        with oo.NoSummaryPhase {

    override protected type TransformerContext = Unit
    override protected def getContext(symbols: s.Symbols): Unit = {}

    override protected def extractFunction(context: TransformerContext, fd: s.FunDef): (t.FunDef, Unit) = {
        val newfd = fd.fullBody match
            case s.Let(a1, a2, body) =>
                val newAssert = s.Assert(s.Equals(s.IntegerLiteral(1), s.IntegerLiteral(1)), None, body)
                fd.copy(fullBody = s.Let(a1, a2, newAssert))
            case _ => fd
        (newfd, ())
    }
}
