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

    private def productType(originalType: s.Type): s.Type =
        t.TupleType(Seq(originalType, originalType))

    private def freshProductValDef(originalValDef: s.ValDef): s.ValDef =
        t.ValDef.fresh(originalValDef.id.name, productType(originalValDef.tpe))

    private def firstExpression(expression: s.Expr): s.Expr =
        expression match
            case s.Tuple(Seq(first, _)) => first
            case _ => s.TupleSelect(expression, 1)

    private def secondExpression(expression: s.Expr): s.Expr =
        expression match
            case s.Tuple(Seq(_, second)) => second
            case _ => s.TupleSelect(expression, 2)


    private def lockstepExpression(expression: s.Expr, idToProductValDef: Map[Identifier, s.ValDef]): s.Expr =
        expression match
            case s.Variable(id, tpe, flags) =>
                idToProductValDef(id).toVariable

            case literal: s.Literal[_] =>
                s.Tuple(Seq(literal, literal))

            case s.Let(valDef, value, body) =>
                val productValDef = freshProductValDef(valDef)
                val productValue = lockstepExpression(value, idToProductValDef)
                val productBody = lockstepExpression(body, idToProductValDef + (valDef.id -> productValDef))

                s.Let(productValDef, productValue, productBody)

            case s.Plus(lhs, rhs) =>
                val lockstepLhs = lockstepExpression(lhs, idToProductValDef)
                val lockstepRhs = lockstepExpression(rhs, idToProductValDef)

                val additionFirst = s.Plus(firstExpression(lockstepLhs), firstExpression(lockstepRhs))
                val additionSecond = s.Plus(secondExpression(lockstepLhs), secondExpression(lockstepRhs))

                s.Tuple(Seq(additionFirst, additionSecond))

            case s.IfExpr(condition, thenBranch, elseBranch) =>
                val lockstepCondition = lockstepExpression(condition, idToProductValDef)
                val lockstepConditionFirst = s.TupleSelect(lockstepCondition, 1)
                val lockstepConditionSecond = s.TupleSelect(lockstepCondition, 2)

                s.Assert(
                    s.Equals(lockstepConditionFirst, lockstepConditionSecond),
                    None,
                    s.IfExpr(
                        lockstepConditionFirst,
                        lockstepExpression(thenBranch, idToProductValDef),
                        lockstepExpression(elseBranch, idToProductValDef)
                    )
                )





    private def instrumentFunction(function: s.FunDef): s.FunDef =
        val idToProductValDef = function.params.map(
            paramValDef => paramValDef.id -> freshProductValDef(paramValDef)
        ).toMap

        val lockstepBody = lockstepExpression(function.fullBody, idToProductValDef)

        val publicVariable = idToProductValDef.values.find(_.id.name == "public").get.toVariable
        val publicVariableFirst = s.TupleSelect(publicVariable, 1)
        val publicVariableSecond = s.TupleSelect(publicVariable, 2)
        val lockstepBodyWithPublicEqualRequire = s.Require(
            s.Equals(publicVariableFirst, publicVariableSecond),
            lockstepBody
        )

        val instrumentedFunction = function.copy(
            params = idToProductValDef.values.toSeq,
            fullBody = lockstepBodyWithPublicEqualRequire,
            returnType = productType(function.returnType)
        )

        instrumentedFunction


    override protected def extractFunction(context: TransformerContext, function: s.FunDef): (t.FunDef, Unit) = {
        val resultFunction =
            if function.flags.exists(_.name == "ctverify") then
                instrumentFunction(function)
            else
                function

        (resultFunction, ())
    }
}
