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

    private def lockstepUnaryOperation(operand: s.Expr, operation: s.Expr => s.Expr,
                                       idToProductValDef: Map[Identifier, s.ValDef]): s.Expr =
        val lockstepOperand = lockstepExpression(operand, idToProductValDef)

        val operationFirst = operation(firstExpression(lockstepOperand))
        val operationSecond = operation(secondExpression(lockstepOperand))

        s.Tuple(Seq(operationFirst, operationSecond))

    private def lockstepBinaryOperation(lhs: s.Expr, rhs: s.Expr, operation: (s.Expr, s.Expr) => s.Expr,
                                        idToProductValDef: Map[Identifier, s.ValDef]): s.Expr =
        val lockstepLhs = lockstepExpression(lhs, idToProductValDef)
        val lockstepRhs = lockstepExpression(rhs, idToProductValDef)

        val operationFirst = operation(firstExpression(lockstepLhs), firstExpression(lockstepRhs))
        val operationSecond = operation(secondExpression(lockstepLhs), secondExpression(lockstepRhs))

        s.Tuple(Seq(operationFirst, operationSecond))


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

            case s.Equals(lhs, rhs) =>
                lockstepBinaryOperation(lhs, rhs, s.Equals.apply, idToProductValDef)

            case s.And(Seq(lhs, rhs)) =>
                lockstepBinaryOperation(lhs, rhs, s.And.apply, idToProductValDef)

            case s.Or(Seq(lhs, rhs)) =>
                lockstepBinaryOperation(lhs, rhs, s.Or.apply, idToProductValDef)

            case s.Implies(lhs, rhs) =>
                lockstepBinaryOperation(lhs, rhs, s.Implies.apply, idToProductValDef)

            case s.Not(operand) =>
                lockstepUnaryOperation(operand, s.Not.apply, idToProductValDef)

            case s.Plus(lhs, rhs) =>
                lockstepBinaryOperation(lhs, rhs, s.Plus.apply, idToProductValDef)

            case s.Minus(lhs, rhs) =>
                lockstepBinaryOperation(lhs, rhs, s.Minus.apply, idToProductValDef)

            case s.UMinus(operand) =>
                lockstepUnaryOperation(operand, s.UMinus.apply, idToProductValDef)

            case s.Times(lhs, rhs) =>
                lockstepBinaryOperation(lhs, rhs, s.Times.apply, idToProductValDef)

            case s.Division(lhs, rhs) =>
                lockstepBinaryOperation(lhs, rhs, s.Division.apply, idToProductValDef)

            case s.Remainder(lhs, rhs) =>
                lockstepBinaryOperation(lhs, rhs, s.Remainder.apply, idToProductValDef)

            case s.Modulo(lhs, rhs) =>
                lockstepBinaryOperation(lhs, rhs, s.Modulo.apply, idToProductValDef)

            case s.LessThan(lhs, rhs) =>
                lockstepBinaryOperation(lhs, rhs, s.LessThan.apply, idToProductValDef)

            case s.GreaterThan(lhs, rhs) =>
                lockstepBinaryOperation(lhs, rhs, s.GreaterThan.apply, idToProductValDef)

            case s.GreaterEquals(lhs, rhs) =>
                lockstepBinaryOperation(lhs, rhs, s.GreaterEquals.apply, idToProductValDef)

            case s.LessEquals(lhs, rhs) =>
                lockstepBinaryOperation(lhs, rhs, s.LessEquals.apply, idToProductValDef)

            case s.IfExpr(condition, thenBranch, elseBranch) =>
                val lockstepCondition = lockstepExpression(condition, idToProductValDef)
                val lockstepConditionFirst = firstExpression(lockstepCondition)
                val lockstepConditionSecond = secondExpression(lockstepCondition)

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
        val publicVariableFirst = firstExpression(publicVariable)
        val publicVariableSecond = secondExpression(publicVariable)
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
