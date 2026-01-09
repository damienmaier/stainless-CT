package stainless
package extraction
package ct

import inox.Context

// Pipeline phase that transforms functions with the "ctverify" flag into
// a lockstep product function, whose validity is equivalent to the
// CT security of the original function
class Instrumentation(override val s: xlang.trees.type, override val t: xlang.trees.type)
                     (using override val context: inox.Context)
    extends oo.IdentityTypeDefs
        with oo.IdentityClasses
        with IdentitySorts
        with IdentityFunctions
        with oo.NoSummaryPhase {

    override protected type TransformerContext = Unit
    override protected def getContext(symbols: s.Symbols): Unit = {}

    // Given a type T from the original expression, returns the product type (T, T)
    // to be used in the lockstep expression
    private def productType(originalType: s.Type): s.Type =
        t.TupleType(Seq(originalType, originalType))

    // Given a ValDef from the original expression, returns a fresh ValDef
    // with appropriate product type to be used in the lockstep expression
    private def freshProductValDef(originalValDef: s.ValDef): s.ValDef =
        t.ValDef.fresh(originalValDef.id.name, productType(originalValDef.tpe))

    // Builds an expression for accessing the first element of a tuple.
    // If the expression is already a tuple expression, its first element is
    // directly extracted to avoid unnecessary TupleSelect nodes.
    private def firstExpression(expression: s.Expr): s.Expr =
        expression match
            case s.Tuple(Seq(first, _)) => first
            case _ => s.TupleSelect(expression, 1)

    // Builds an expression for accessing the second element of a tuple.
    // If the expression is already a tuple expression, its second element is
    // directly extracted to avoid unnecessary TupleSelect nodes.
    private def secondExpression(expression: s.Expr): s.Expr =
        expression match
            case s.Tuple(Seq(_, second)) => second
            case _ => s.TupleSelect(expression, 2)

    // Helper method for building lockstep unary operations
    private def lockstepUnaryOperation(operand: s.Expr, operation: s.Expr => s.Expr)
                                      (using idToProductValDef: Map[Identifier, s.ValDef]): s.Expr =
        val lockstepOperand = lockstepExpression(operand)

        val operationFirst = operation(firstExpression(lockstepOperand))
        val operationSecond = operation(secondExpression(lockstepOperand))

        s.Tuple(Seq(operationFirst, operationSecond))

    // Helper method for building lockstep binary operations.
    // If checkShortCircuit is true, an assertion is added to ensure that
    // `lhs` evaluates to the same value in both executions.
    private def lockstepBinaryOperation(lhs: s.Expr, rhs: s.Expr, operation: (s.Expr, s.Expr) => s.Expr,
                                        originalExpression: Option[s.Expr] = None, checkShortCircuit: Boolean = false)
                                       (using idToProductValDef: Map[Identifier, s.ValDef]): s.Expr =
        val lockstepLhs = lockstepExpression(lhs)
        val lockstepRhs = lockstepExpression(rhs)

        val operationFirst = operation(firstExpression(lockstepLhs), firstExpression(lockstepRhs))
        val operationSecond = operation(secondExpression(lockstepLhs), secondExpression(lockstepRhs))

        val result = s.Tuple(Seq(operationFirst, operationSecond))

        val assertionPredicate = s.Equals(firstExpression(lockstepLhs), secondExpression(lockstepLhs))

        val assertionPredicateWitLocation = originalExpression match
            // adds the location in source file, which gives better user feedback
            case Some(expr) => assertionPredicate.copiedFrom(expr)
            case None => assertionPredicate

        if checkShortCircuit then
            s.Assert(assertionPredicate,
                Some("Short-circuiting should not depend on the secret"),
                result
            )
        else
            result


    // performs a deep copy of a match case pattern, where the new binders
    // are fresh ValDefs whose names are postfixed with `binderPostfix`
    private def copyPattern(pattern: s.Pattern, binderPostfix: String): s.Pattern =

        def freshBinder(binder: Option[s.ValDef]): Option[s.ValDef] =
            binder.map(b => s.ValDef.fresh(b.id.name + binderPostfix, b.tpe))

        pattern match
            case s.WildcardPattern(binder) =>
                s.WildcardPattern(freshBinder(binder))
            case s.ClassPattern(binder, tpe, subPatterns) =>
                s.ClassPattern(freshBinder(binder), tpe, subPatterns.map(copyPattern(_, binderPostfix)))
            case s.TuplePattern(binder, subPatterns) =>
                s.TuplePattern(freshBinder(binder), subPatterns.map(copyPattern(_, binderPostfix)))
            case s.LiteralPattern(binder, literal) =>
                s.LiteralPattern(freshBinder(binder), literal)
            // TODO are all pattern cases covered?

    // Computes the lockstep version of a match case
    private def lockstepMatchCase(matchCase: s.MatchCase)(using idToProductValDef: Map[Identifier, s.ValDef]): s.MatchCase =
        // TODO guards are currently not supported
        val s.MatchCase(pattern, _, expression) = matchCase
        val patternFirst = copyPattern(pattern, "_first")
        val patternSecond = copyPattern(pattern, "_second")

        // Generate the new valdefs for the original binders
        // the lockstep version of the rhs expression should use those new valdefs
        val newIdToProductValDef = (
            for originalValDef <- pattern.binders
                yield originalValDef.id -> freshProductValDef(originalValDef)
            ).toMap

        val lockstepMatchCaseExpression =
            lockstepExpression(expression)(using idToProductValDef ++ newIdToProductValDef)

        // Add at the top of the new rhs expression the let expressions
        // that connect the pairs of binders to single variables
        val expressionWithDefs =
            newIdToProductValDef.values.zip(patternFirst.binders.zip(patternSecond.binders))
                .foldLeft(lockstepMatchCaseExpression):
                    case (currentExpression, (productValDef, (firstValDef, secondValDef))) =>
                        s.Let(
                            productValDef,
                            s.Tuple(Seq(firstValDef.toVariable, secondValDef.toVariable)),
                            currentExpression
                        )

        s.MatchCase(
            s.TuplePattern(None, Seq(patternFirst, patternSecond)),
            None,
            expressionWithDefs
        )


    // Builds a lockstep expression whose evaluation simulates two simultaneous evaluations of `experession`.
    // The new expression returns a tuple of the results of both evaluations.
    private def lockstepExpression(expression: s.Expr)(using idToProductValDef: Map[Identifier, s.ValDef]): s.Expr =
        expression match
            case s.Variable(id, tpe, flags) =>
                idToProductValDef(id).toVariable

            case literal: s.Literal[_] =>
                s.Tuple(Seq(literal, literal))

            case s.Let(valDef, value, body) =>
                val productValDef = freshProductValDef(valDef)
                val productValue = lockstepExpression(value)
                // the variables referring to `valDef` in `body` should now refer to `productValDef`
                val productBody = lockstepExpression(body)(using idToProductValDef + (valDef.id -> productValDef))

                val resultLetExpression = s.Let(productValDef, productValue, productBody)

                // the user can declare any expression as public by creating a variable definition
                // with the "public" flag
                if valDef.flags.exists(_.name == "public") then
                    s.Require(
                        s.Equals(firstExpression(productValue), secondExpression(productValue)),
                        resultLetExpression
                    )
                else
                    resultLetExpression


            case s.Tuple(Seq(leftExpression, rightExpression)) =>
                val lockstepLeft = lockstepExpression(leftExpression)
                val lockstepRight = lockstepExpression(rightExpression)

                val lockstepFirst = s.Tuple(Seq(firstExpression(lockstepLeft), firstExpression(lockstepRight)))
                val lockstepSecond = s.Tuple(Seq(secondExpression(lockstepLeft), secondExpression(lockstepRight)))

                s.Tuple(Seq(lockstepFirst, lockstepSecond))


            case s.Equals(lhs, rhs) =>
                lockstepBinaryOperation(lhs, rhs, s.Equals.apply)

            case expr @ s.And(Seq(lhs, rhs)) =>
                lockstepBinaryOperation(lhs, rhs, s.And.apply, Some(expr), true)

            case expr @ s.Or(Seq(lhs, rhs)) =>
                lockstepBinaryOperation(lhs, rhs, s.Or.apply, Some(expr), true)

            case s.BoolBitwiseAnd(lhs, rhs) =>
                lockstepBinaryOperation(lhs, rhs, s.BoolBitwiseAnd.apply)

            case s.BoolBitwiseOr(lhs, rhs) =>
                lockstepBinaryOperation(lhs, rhs, s.BoolBitwiseOr.apply)

            case s.Not(operand) =>
                lockstepUnaryOperation(operand, s.Not.apply)

            case s.Plus(lhs, rhs) =>
                lockstepBinaryOperation(lhs, rhs, s.Plus.apply)

            case s.Minus(lhs, rhs) =>
                lockstepBinaryOperation(lhs, rhs, s.Minus.apply)

            case s.UMinus(operand) =>
                lockstepUnaryOperation(operand, s.UMinus.apply)

            case s.Times(lhs, rhs) =>
                lockstepBinaryOperation(lhs, rhs, s.Times.apply)

            case s.Division(lhs, rhs) =>
                lockstepBinaryOperation(lhs, rhs, s.Division.apply)

            case s.Remainder(lhs, rhs) =>
                lockstepBinaryOperation(lhs, rhs, s.Remainder.apply)

            case s.Modulo(lhs, rhs) =>
                lockstepBinaryOperation(lhs, rhs, s.Modulo.apply)

            case s.LessThan(lhs, rhs) =>
                lockstepBinaryOperation(lhs, rhs, s.LessThan.apply)

            case s.GreaterThan(lhs, rhs) =>
                lockstepBinaryOperation(lhs, rhs, s.GreaterThan.apply)

            case s.GreaterEquals(lhs, rhs) =>
                lockstepBinaryOperation(lhs, rhs, s.GreaterEquals.apply)

            case s.LessEquals(lhs, rhs) =>
                lockstepBinaryOperation(lhs, rhs, s.LessEquals.apply)

            case ifExpr @ s.IfExpr(condition, thenBranch, elseBranch) =>
                val lockstepCondition = lockstepExpression(condition)
                val lockstepConditionFirst = firstExpression(lockstepCondition)
                val lockstepConditionSecond = secondExpression(lockstepCondition)

                s.Assert(
                    s.Equals(lockstepConditionFirst, lockstepConditionSecond).copiedFrom(ifExpr),
                    Some("The if condition should not depend on the secret"),
                    s.IfExpr(
                        // as we have asserted that both executions take the same branch,
                        // we can use either condition for the lockstep if expression
                        lockstepConditionFirst,
                        lockstepExpression(thenBranch),
                        lockstepExpression(elseBranch)
                    )
                )

            case matchExpr @ s.MatchExpr(scrutinee, matchCases) =>

                // builds a new pattern matching expression whose patterns are identical to the original ones,
                // but whose rhs expressions return the index of the matched case
                val executionPathMatchCases = matchCases.zipWithIndex.map:
                    (matchCase, pathIndex) => matchCase.copy(rhs = s.IntegerLiteral(pathIndex))

                val lockstepScrutinee = lockstepExpression(scrutinee)

                // expression that computes the execution path index for the first execution
                val executionPathMatchExpressionFirst = s.MatchExpr(
                    firstExpression(lockstepScrutinee),
                    executionPathMatchCases
                )
                // expression that computes the execution path index for the second execution
                val executionPathMatchExpressionSecond = s.MatchExpr(
                    secondExpression(lockstepScrutinee),
                    executionPathMatchCases
                )

                s.Assert(
                    // ensure that both executions take the same branch
                    s.Equals(executionPathMatchExpressionFirst, executionPathMatchExpressionSecond)
                        .copiedFrom(matchExpr),
                    Some("The match case condition should not depend on the secret"),
                    s.MatchExpr(
                        lockstepScrutinee,
                        matchCases.map(lockstepMatchCase)
                    )
                )

            case s.FunctionInvocation(id, tps, arguments) =>
                s.FunctionInvocation(id, tps, arguments.map(lockstepExpression))

            case s.Require(predicate, body) =>
                val lockstepPredicate = lockstepExpression(predicate)
                s.Require(
                    firstExpression(lockstepPredicate),
                    s.Require(
                        secondExpression(lockstepPredicate),
                        lockstepExpression(body)
                    )
                )

            case s.MethodInvocation(receiver, id, tps, arguments) =>
                val lockstepReceiver = lockstepExpression(receiver)
                val firstRecveiver = firstExpression(lockstepReceiver)
                val secondReceiver = secondExpression(lockstepReceiver)

                val lockstepArguments = arguments.map(lockstepExpression)
                val firstArguments = lockstepArguments.map(firstExpression)
                val secondArguments = lockstepArguments.map(secondExpression)

                s.Tuple(Seq(
                    s.MethodInvocation(firstRecveiver, id, tps, firstArguments),
                    s.MethodInvocation(secondReceiver, id, tps, secondArguments)
                ))


    // Computes the lockstep version of a function
    private def instrumentFunction(function: s.FunDef): s.FunDef =
        // compute the new valdefs for the function parameters
        val idToProductValDef = function.params.map(
            paramValDef => paramValDef.id -> freshProductValDef(paramValDef)
        ).toMap

        val lockstepBody = lockstepExpression(function.fullBody)(using idToProductValDef)

        // for each public parameter, add a require that both executions receive the same value
        val publicVariableValDefs = function.params.filterNot(_.flags.exists(_.name == "secret"))
        val lockstepBodyWithPublicEqualRequire = publicVariableValDefs.foldLeft(lockstepBody):
            (currentBody, publicValDef) =>
                val publicVariable = idToProductValDef(publicValDef.id).toVariable
                val publicVariableFirst = firstExpression(publicVariable)
                val publicVariableSecond = secondExpression(publicVariable)
                s.Require(
                    s.Equals(publicVariableFirst, publicVariableSecond),
                    currentBody
                )

        function.copy(
            params = idToProductValDef.values.toSeq,
            fullBody = lockstepBodyWithPublicEqualRequire,
            returnType = productType(function.returnType)
        )


    // The entry point of this pipeline phase
    // Transforms functions with the "ctverify" flag using the instrumentation procedure
    override protected def extractFunction(context: TransformerContext, function: s.FunDef): (t.FunDef, Unit) = {
        val resultFunction =
            if function.flags.exists(_.name == "ctverify") then
                instrumentFunction(function)
            else
                function

        (resultFunction, ())
    }
}
