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

    private def freshShadowId(id: Identifier): Identifier =
        FreshIdentifier(id.name + "_shadow")

    private def shadowExpression(expression: s.Expr, idToShadowId: Map[Identifier, Identifier]): s.Expr =

        def updateToShadowVariableIfApplicable(source: s.exprOps.Source):  Option[s.exprOps.Source] =
            source match
                case s.Variable(id, tpe, flags) if idToShadowId.contains(id) =>
                    Some(s.Variable(idToShadowId(id), tpe, flags))
                case _ =>
                    None

        s.exprOps.preMap(updateToShadowVariableIfApplicable)(expression)

    private def lockstepExpression(expression: s.Expr, idToShadowId: Map[Identifier, Identifier]): s.Expr =
        expression match
            case s.Let(valDef, value, body) =>
                val shadowValDefId = freshShadowId(valDef.id)

                val lockstepValue = lockstepExpression(value, idToShadowId)
                val lockstepBody = lockstepExpression(body, idToShadowId + (valDef.id -> shadowValDefId))

                val newLet = s.Let(valDef, lockstepValue, lockstepBody)

                val shadowValDef = s.ValDef(shadowValDefId, valDef.tpe, valDef.flags)
                val shadowValue = shadowExpression(value, idToShadowId)

                s.Let(
                    shadowValDef,
                    shadowValue,
                    newLet
                )

            case s.IfExpr(condition, thenBranch, elseBranch) =>
                val lockstepCondition = lockstepExpression(condition, idToShadowId)
                val lockstepThenBranch = lockstepExpression(thenBranch, idToShadowId)
                val lockstepElseBranch = lockstepExpression(elseBranch, idToShadowId)

                val newIfExpr = s.IfExpr(lockstepCondition, lockstepThenBranch, lockstepElseBranch)

                val shadowCondition = shadowExpression(condition, idToShadowId)
                val assertPredicate = s.Equals(condition, shadowCondition)

                s.Assert(
                    assertPredicate,
                    None,
                    newIfExpr
                )
            case _ =>
                expression

    override protected def extractFunction(context: TransformerContext, function: s.FunDef): (t.FunDef, Unit) = {
        val secretArgumentId = function.params.find(_.id.name == "secret").get.id
        val publicArgumentId = function.params.find(_.id.name == "public").get.id

        val idToShadowId = Map(
            secretArgumentId -> freshShadowId(secretArgumentId),
            publicArgumentId -> freshShadowId(publicArgumentId)
        )

        val shadowSecretArgumentValDef = s.ValDef(idToShadowId(secretArgumentId), s.IntegerType())
        val shadowPublicArgumentValDef = s.ValDef(idToShadowId(publicArgumentId), s.IntegerType())

        val lockstepBody = lockstepExpression(function.fullBody, idToShadowId)

        val lockstepBodyWithShadowPublic = s.Let(
            shadowPublicArgumentValDef,
            s.Variable(publicArgumentId, s.IntegerType(), Seq.empty),
            lockstepBody
        )

        val instrumentedFunction = function.copy(
            params = function.params :+ shadowSecretArgumentValDef,
            fullBody = lockstepBodyWithShadowPublic
        )

        (instrumentedFunction, ())
    }
}
