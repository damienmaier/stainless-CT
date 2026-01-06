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


    private def lockstepExpression(expression: s.Expr, idToProductValDef: Map[Identifier, s.ValDef]): s.Expr =
        expression match
            case s.Variable(id, tpe, flags) =>
                idToProductValDef(id).toVariable

            case literal: s.Literal[_] =>
                s.Tuple(Seq(literal, literal))

            case s.Let(valDef, value, body) =>
                val productValDef = t.ValDef.fresh(valDef.id.name, productType(valDef.tpe))
                val productValue = lockstepExpression(value, idToProductValDef)
                val productBody = lockstepExpression(body, idToProductValDef + (valDef.id -> productValDef))

                s.Let(productValDef, productValue, productBody)

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
        val originalSecretValDef = function.params.find(_.id.name == "secret").get
        val originalPublicValDef = function.params.find(_.id.name == "public").get

        val productSecretValDef = t.ValDef.fresh("secret", productType(originalSecretValDef.tpe))
        val productPublicValDef = t.ValDef.fresh("public", productType(originalPublicValDef.tpe))

        val idToProductId = Map(
            originalSecretValDef.id -> productSecretValDef,
            originalPublicValDef.id -> productPublicValDef
        )

        val lockstepBody = lockstepExpression(function.fullBody, idToProductId)

        val originalPublicVariable = s.Variable(originalPublicValDef.id, originalPublicValDef.tpe, Seq.empty)
        val lockstepBodyWithProductPublicInitialization = s.Let(
            productPublicValDef,
            s.Tuple(Seq(originalPublicVariable, originalPublicVariable)),
            lockstepBody
        )

        val instrumentedFunction = function.copy(
            params = Seq(productSecretValDef, originalPublicValDef),
            fullBody = lockstepBodyWithProductPublicInitialization,
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
