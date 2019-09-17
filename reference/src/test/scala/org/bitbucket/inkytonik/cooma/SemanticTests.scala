/*
 * This file is part of Cooma.
 *
 * Copyright (C) 2019 Anthony M Sloane, Macquarie University.
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package org.bitbucket.inkytonik.cooma

import org.bitbucket.inkytonik.kiama.util.Tests

class SemanticTests extends Tests {

    import org.bitbucket.inkytonik.cooma.CoomaParserSyntax._
    import org.bitbucket.inkytonik.kiama.relation.Tree
    import org.bitbucket.inkytonik.kiama.util.StringSource

    val driver = new ReferenceDriver
    val config = {
        val newConfig = driver.createConfig(Seq())
        newConfig.verify()
        newConfig
    }

    case class SemanticTest(
        name : String,
        expression : String,
        expectedMessages : String
    )

    val semanticTests =
        Vector(
            // Definitions

            SemanticTest(
                "distinct argument names",
                "fun(x : Int, y : Int) = x",
                ""
            ),
            SemanticTest(
                "duplicated argument names",
                "fun(x : Int, x : Int) = x",
                """|1:5:error: x is declared more than once
                   |fun(x : Int, x : Int) = x
                   |    ^
                   |1:14:error: x is declared more than once
                   |fun(x : Int, x : Int) = x
                   |             ^
                   |"""
            ),
            SemanticTest(
                "distinct field names",
                "{x = 1, y = 1}",
                ""
            ),
            SemanticTest(
                "duplicate field names",
                "{x = 1, x = 1}",
                """|1:2:error: duplicate field name x
                   |{x = 1, x = 1}
                   | ^
                   |1:9:error: duplicate field name x
                   |{x = 1, x = 1}
                   |        ^
                   |"""
            ),
            SemanticTest(
                "distinct type field names",
                "fun (a : {x : Int, y : Int}) = 0",
                ""
            ),
            SemanticTest(
                "duplicate type field names",
                "fun (a : {x : Int, x : Int}) = 0",
                """|1:11:error: duplicate type field name x
                   |fun (a : {x : Int, x : Int}) = 0
                   |          ^
                   |1:20:error: duplicate type field name x
                   |fun (a : {x : Int, x : Int}) = 0
                   |                   ^
                   |"""
            ),
            SemanticTest(
                "distinct function names",
                "{ def f(i : Int) : Int = i def g(i : Int) : Int = i 0 }",
                ""
            ),
            SemanticTest(
                "duplicate function names in same group",
                "{ def f(i : Int) : Int = i def f(i : Int) : Int = i 0 }",
                """|1:7:error: f is declared more than once
                   |{ def f(i : Int) : Int = i def f(i : Int) : Int = i 0 }
                   |      ^
                   |1:32:error: f is declared more than once
                   |{ def f(i : Int) : Int = i def f(i : Int) : Int = i 0 }
                   |                               ^
                   |"""
            ),

            // Uses

            SemanticTest(
                "lone name",
                "x",
                """|1:1:error: x is not declared
                   |x
                   |^
                   |"""
            ),
            SemanticTest(
                "declared value name",
                "{ val x = 1 x}",
                ""
            ),
            SemanticTest(
                "not-declared value name",
                "{ val x = 1 y}",
                """|1:13:error: y is not declared
                   |{ val x = 1 y}
                   |            ^
                   |"""
            ),
            SemanticTest(
                "declared argument name",
                "fun (x : Int) = x",
                ""
            ),
            SemanticTest(
                "not-declared use in no argument function",
                "fun () = x",
                """|1:10:error: x is not declared
                   |fun () = x
                   |         ^
                   |"""
            ),
            SemanticTest(
                "not-declared use in argument function",
                "fun (x : Int) = y",
                """|1:17:error: y is not declared
                   |fun (x : Int) = y
                   |                ^
                   |"""
            ),
            SemanticTest(
                "not-declared use in nested expression",
                "fun (x : {a : Int}) = x & y",
                """|1:27:error: y is not declared
                   |fun (x : {a : Int}) = x & y
                   |                          ^
                   |"""
            ),
            SemanticTest(
                "not-declared use in field definition",
                "fun () = {a = y}",
                """|1:15:error: y is not declared
                   |fun () = {a = y}
                   |              ^
                   |"""
            ),
            SemanticTest(
                "not-declared use in value definition (self)",
                "{ val x = x 0 }",
                """|1:11:error: x is not declared
                   |{ val x = x 0 }
                   |          ^
                   |"""
            ),
            SemanticTest(
                "not-declared use in value definition (other)",
                "{ val x = y 0 }",
                """|1:11:error: y is not declared
                   |{ val x = y 0 }
                   |          ^
                   |"""
            ),
            SemanticTest(
                "overriding value names",
                """{ val x = "hi" val x = 2 {fun (a : Int) = 0}(x) }""",
                ""
            ),
            SemanticTest(
                "not-declared use in no argument function definition",
                "{ def f () : Int = x 0 }",
                """|1:20:error: x is not declared
                   |{ def f () : Int = x 0 }
                   |                   ^
                   |"""
            ),
            SemanticTest(
                "not-declared use in argument function definition",
                "{ def f (x : Int) : Int = y 0 }",
                """|1:27:error: y is not declared
                   |{ def f (x : Int) : Int = y 0 }
                   |                          ^
                   |"""
            ),
            SemanticTest(
                "not-declared use as type name in function",
                "fun (x : Foo) = 0",
                """|1:10:error: Foo is not declared
                   |fun (x : Foo) = 0
                   |         ^
                   |"""
            ),
            SemanticTest(
                "not-declared use as type name in function defintion",
                "{ def f (x : Foo) : Int = 0 0 }",
                """|1:14:error: Foo is not declared
                   |{ def f (x : Foo) : Int = 0 0 }
                   |             ^
                   |"""
            ),
            SemanticTest(
                "overriding function names in different group",
                "{ def f(i : String) : Int = 0 val x = 1 def f(i : Int) : Int = i f(0) }",
                ""
            ),

            // Application

            SemanticTest(
                "apply no-arg function",
                "{fun () = 0}()",
                ""
            ),
            SemanticTest(
                "apply function to too many arguments (zero)",
                "{fun () = 0}(3)",
                """|1:14:error: expected no arguments, got 1
                   |{fun () = 0}(3)
                   |             ^
                   |"""
            ),
            SemanticTest(
                "apply function to too many arguments (one)",
                "{fun (x : Int) = 0}(2, 3)",
                """|1:21:error: expected up to one argument, got 2
                   |{fun (x : Int) = 0}(2, 3)
                   |                    ^
                   |"""
            ),
            SemanticTest(
                "apply function to too many arguments (more than one)",
                "{fun (x : Int, y : Int) = 0}(2, 3, 4)",
                """|1:30:error: expected up to 2 arguments, got 3
                   |{fun (x : Int, y : Int) = 0}(2, 3, 4)
                   |                             ^
                   |"""
            ),
            SemanticTest(
                "application of non-function",
                "4(2, 3)",
                """|1:1:error: application of non-function type Int
                   |4(2, 3)
                   |^
                   |"""
            ),

            // Pre-defined uses

            SemanticTest(
                "Reader is a record with a read field",
                "fun (r : Reader) = r.read()",
                ""
            ),
            SemanticTest(
                "Reader read field has correct type",
                "{ def f (r : Reader) : String = r.read() 0 }",
                ""
            ),
            SemanticTest(
                "Reader doesn't have non-read field",
                "fun (r : Reader) = r.foo",
                """|1:22:error: foo is not a field of record type {read : () => String}
                   |fun (r : Reader) = r.foo
                   |                     ^
                   |"""
            ),
            SemanticTest(
                "Writer is pre-defined record type",
                """fun (w : Writer) = w.write("hello")""",
                ""
            ),
            SemanticTest(
                "Writer write field has correct type",
                """{ def f (w : Writer) : Unit = w.write("hi") 0 }""",
                ""
            ),
            SemanticTest(
                "Writer doesn't have non-write field",
                "fun (w : Writer) = w.foo",
                """|1:22:error: foo is not a field of record type {write : (String) => Unit}
                   |fun (w : Writer) = w.foo
                   |                     ^
                   |"""
            ),
            SemanticTest(
                "ReaderWriter is pre-defined record type",
                "fun (rw : ReaderWriter) = { val s = rw.read() rw.write(s) }",
                ""
            ),
            SemanticTest(
                "ReaderWriter read field has correct type",
                "{ def f (rw : ReaderWriter) : String = rw.read() 0 }",
                ""
            ),
            SemanticTest(
                "ReaderWriter write field has correct type",
                """{ def f (rw : ReaderWriter) : Unit = rw.write("hi") 0 }""",
                ""
            ),
            SemanticTest(
                "ReaderWriter doesn't have non-write field",
                "fun (rw : ReaderWriter) = rw.foo",
                """|1:30:error: foo is not a field of record type {read : () => String, write : (String) => Unit}
                   |fun (rw : ReaderWriter) = rw.foo
                   |                             ^
                   |"""
            ),

            // Selection

            SemanticTest(
                "existent field name (one)",
                "{x = 3}.x",
                ""
            ),
            SemanticTest(
                "existent field name (many)",
                "{x = 3, y = 4, z = 5}.y",
                ""
            ),
            SemanticTest(
                "non-existent field name (one)",
                "{x = 3}.y",
                """|1:9:error: y is not a field of record type {x : Int}
                   |{x = 3}.y
                   |        ^
                   |"""
            ),
            SemanticTest(
                "non-existent field name (many)",
                "{x = 3, y = 4, z = 5}.w",
                """|1:23:error: w is not a field of record type {x : Int, y : Int, z : Int}
                   |{x = 3, y = 4, z = 5}.w
                   |                      ^
                   |"""
            ),
            SemanticTest(
                "selection from non-record",
                "42.x",
                """|1:4:error: selection of x field from non-record type Int
                   |42.x
                   |   ^
                   |"""
            ),

            // Type names

            SemanticTest(
                "non-type name used as argument type",
                "{ val x = 1 fun (y : x) = y }",
                """|1:22:error: expected Type, got Int
                   |{ val x = 1 fun (y : x) = y }
                   |                     ^
                   |"""
            ),
            SemanticTest(
                "non-type name used as argument type in function type",
                "{ val x = 1 fun (y : (x) => Int) = y }",
                """|1:23:error: expected Type, got Int
                   |{ val x = 1 fun (y : (x) => Int) = y }
                   |                      ^
                   |"""
            ),
            SemanticTest(
                "non-type name used as return type in function type",
                "{ val x = 1 fun (y : (Int) => x) = y }",
                """|1:31:error: expected Type, got Int
                   |{ val x = 1 fun (y : (Int) => x) = y }
                   |                              ^
                   |"""
            ),
            SemanticTest(
                "non-type name used as field type",
                "{ val x = 1 fun (y : {a : x}) = 1 }",
                """|1:27:error: expected Type, got Int
                   |{ val x = 1 fun (y : {a : x}) = 1 }
                   |                          ^
                   |"""
            ),

            // type aliases

            SemanticTest(
                "alias of simple type",
                "{ val Foo = Int {fun (x : Foo) = 0}(1) }",
                ""
            ),
            SemanticTest(
                "alias of record type",
                "{ val Foo = {x : Int, y : String} fun (f : Foo) = f.x }",
                ""
            ),
            SemanticTest(
                "alias of function type",
                "{ val Foo = (Int) => String fun (f : Foo) = f(0) }",
                ""
            ),
            SemanticTest(
                "alias of alias of simple type",
                "{ val Foo = Int val Bar = Foo {fun (x : Bar) = 0}(1) }",
                ""
            ),
            SemanticTest(
                "alias of record type of alias",
                """{
                  |   val Foo = Int
                  |   val Bar = {f : Foo}
                  |   def m (x : Bar) : Int = x.f
                  |   0
                  |}
                  |""",
                ""
            ),
            SemanticTest(
                "alias of function type of alias",
                """{
                  |   val Foo = Int
                  |   val Bar = (Foo) => Foo
                  |   def m (x : Bar) : Int = x(0)
                  |   0
                  |}
                  |""",
                ""
            ),
            SemanticTest(
                "alias of not-declared type",
                "{ val Foo = Bar 0 }",
                """|1:13:error: Bar is not declared
                   |{ val Foo = Bar 0 }
                   |            ^
                   |"""
            ),
            SemanticTest(
                "alias of self",
                "{ val Foo = Foo 0 }",
                """|1:13:error: Foo is not declared
                   |{ val Foo = Foo 0 }
                   |            ^
                   |"""
            ),

            // Expected types

            // - ok arguments

            SemanticTest(
                "function argument type exact match (one)",
                "{fun (x : Int) = x}(1)",
                ""
            ),
            SemanticTest(
                "function argument type exact match (two)",
                "{fun (x : Int, y : Int) = x}(1, 2)",
                ""
            ),
            SemanticTest(
                "function definition argument type exact match (one)",
                "{ def f (x : Int) : Int = x f(1) }",
                ""
            ),
            SemanticTest(
                "function definition argument type exact match (two)",
                "{ def f (x : Int, y : Int) : Int = x f(1, 2) }",
                ""
            ),

            // - bad arguments

            SemanticTest(
                "bad function argument type (one, simple)",
                "{fun (x : String) = x}(1)",
                """|1:24:error: expected String, got Int
                   |{fun (x : String) = x}(1)
                   |                       ^
                   |"""
            ),
            SemanticTest(
                "bad function argument type (two, simple)",
                "{fun (x : Int, y : String) = x}(1, 2)",
                """|1:36:error: expected String, got Int
                   |{fun (x : Int, y : String) = x}(1, 2)
                   |                                   ^
                   |"""
            ),
            SemanticTest(
                "bad function argument type (record formal)",
                "{fun (x : {y : Int}) = x}(1)",
                """|1:27:error: expected {y : Int}, got Int
                   |{fun (x : {y : Int}) = x}(1)
                   |                          ^
                   |"""
            ),
            SemanticTest(
                "bad function argument type (record actual)",
                "{fun (x : Int) = x}({y = 1})",
                """|1:21:error: expected Int, got {y : Int}
                   |{fun (x : Int) = x}({y = 1})
                   |                    ^
                   |"""
            ),
            SemanticTest(
                "bad function argument type (function formal)",
                "{fun (x : (Int) => String) = x}(1)",
                """|1:33:error: expected (Int) => String, got Int
                   |{fun (x : (Int) => String) = x}(1)
                   |                                ^
                   |"""
            ),
            SemanticTest(
                "bad function argument type (function actual)",
                "{fun (x : Int) = x}(fun (y : Int) = y)",
                """|1:21:error: expected Int, got (Int) => Int
                   |{fun (x : Int) = x}(fun (y : Int) = y)
                   |                    ^
                   |"""
            ),
            SemanticTest(
                "bad function definition argument type (one, simple)",
                "{ def f (x : String) : Int = 0 f(1) }",
                """|1:34:error: expected String, got Int
                   |{ def f (x : String) : Int = 0 f(1) }
                   |                                 ^
                   |"""
            ),
            SemanticTest(
                "bad function definition argument type (two, simple)",
                "{ def f (x : Int, y : String) : Int = x f(1, 2) }",
                """|1:46:error: expected String, got Int
                   |{ def f (x : Int, y : String) : Int = x f(1, 2) }
                   |                                             ^
                   |"""
            ),
            SemanticTest(
                "bad function definition argument type (record formal)",
                "{ def f (x : {y : Int}) : Int = 0 f(1) }",
                """|1:37:error: expected {y : Int}, got Int
                   |{ def f (x : {y : Int}) : Int = 0 f(1) }
                   |                                    ^
                   |"""
            ),
            SemanticTest(
                "bad function definition argument type (record actual)",
                "{ def f (x : Int) : Int = x f({y = 1}) }",
                """|1:31:error: expected Int, got {y : Int}
                   |{ def f (x : Int) : Int = x f({y = 1}) }
                   |                              ^
                   |"""
            ),
            SemanticTest(
                "bad function definition argument type (function formal)",
                "{ def f (x : (Int) => String) : Int = 0 f(1) }",
                """|1:43:error: expected (Int) => String, got Int
                   |{ def f (x : (Int) => String) : Int = 0 f(1) }
                   |                                          ^
                   |"""
            ),
            SemanticTest(
                "bad function definition argument type (function actual)",
                "{ def f (x : Int) : Int = x f(fun (y : Int) = y) }",
                """|1:31:error: expected Int, got (Int) => Int
                   |{ def f (x : Int) : Int = x f(fun (y : Int) = y) }
                   |                              ^
                   |"""
            ),

            // - return types

            SemanticTest(
                "bad function definition return type",
                "{ def f (x : Int) : Int = {x = 1} f(0) }",
                """|1:27:error: expected Int, got {x : Int}
                   |{ def f (x : Int) : Int = {x = 1} f(0) }
                   |                          ^
                   |"""
            ),

            // - subtype arguments

            SemanticTest(
                "subtype record function argument",
                "{fun (r : {x : Int}) = 0}({x = 1, y = 2})",
                ""
            ),
            SemanticTest(
                "subtype record function definition argument",
                "{ def f (r : {x : Int}) : Int = 0 f({x = 1, y = 2}) }",
                ""
            ),
            SemanticTest(
                "bad subtype record function argument",
                "{fun (r : {x : Int, y : Int}) = 0}({x = 1})",
                """|1:36:error: expected {x : Int, y : Int}, got {x : Int}
                   |{fun (r : {x : Int, y : Int}) = 0}({x = 1})
                   |                                   ^
                   |"""
            ),
            SemanticTest(
                "bad subtype record function definition argument",
                "{ def f (r : {x : Int, y : Int}) : Int = 0 f({x = 1}) }",
                """|1:46:error: expected {x : Int, y : Int}, got {x : Int}
                   |{ def f (r : {x : Int, y : Int}) : Int = 0 f({x = 1}) }
                   |                                             ^
                   |"""
            ),
            SemanticTest(
                "subtype function function argument",
                "{fun (r : ({x : Int, y : Int}) => Int) = 0}(fun (s : {x : Int}) = s.x)",
                ""
            ),
            SemanticTest(
                "subtype function function definition argument",
                "{ def f (r : ({x : Int, y : Int}) => Int) : Int = 0 f(fun (s : {x : Int}) = 0) }",
                ""
            ),
            SemanticTest(
                "bad subtype function function argument",
                "{fun (r : ({x : Int}) => Int) = 0}(fun (s : {x : Int, y : Int}) = s.x)",
                """|1:36:error: expected ({x : Int}) => Int, got ({x : Int, y : Int}) => Int
                   |{fun (r : ({x : Int}) => Int) = 0}(fun (s : {x : Int, y : Int}) = s.x)
                   |                                   ^
                   |"""
            ),
            SemanticTest(
                "bad subtype function function definition argument",
                "{ def f (r : ({x : Int}) => Int) : Int = 0 f(fun (s : {x : Int, y : Int}) = s.x) }",
                """|1:46:error: expected ({x : Int}) => Int, got ({x : Int, y : Int}) => Int
                   |{ def f (r : ({x : Int}) => Int) : Int = 0 f(fun (s : {x : Int, y : Int}) = s.x) }
                   |                                             ^
                   |"""
            ),

            // - record operations

            SemanticTest(
                "record concatenation (single)",
                "{x = 1} & {y = 2}",
                ""
            ),
            SemanticTest(
                "record concatenation (multiple)",
                "{w = 0, x = 1} & {a = 2, b = 3, c = 4}",
                ""
            ),
            SemanticTest(
                "bad record concatenation (left)",
                "3 & {x = 1}",
                """|1:1:error: expected record type, got Int
                   |3 & {x = 1}
                   |^
                   |"""
            ),
            SemanticTest(
                "bad record concatenation (right)",
                "{x = 1} & 3",
                """|1:11:error: expected record type, got Int
                   |{x = 1} & 3
                   |          ^
                   |"""
            ),
            SemanticTest(
                "bad record concatenation (both)",
                "3 & 4",
                """|1:1:error: expected record type, got Int
                   |3 & 4
                   |^
                   |1:5:error: expected record type, got Int
                   |3 & 4
                   |    ^
                   |"""
            ),
            SemanticTest(
                "bad record concatenation (overlapping field)",
                "{x = 1} & {y = 1, x = 2}",
                """|1:1:error: record concatenation has overlapping fields x
                   |{x = 1} & {y = 1, x = 2}
                   |^
                   |"""
            ),
            SemanticTest(
                "bad record concatenation (overlapping fields)",
                "{w = 0, x = 1, y = 2} & {y = 1, x = 2}",
                """|1:1:error: record concatenation has overlapping fields x, y
                   |{w = 0, x = 1, y = 2} & {y = 1, x = 2}
                   |^
                   |"""
            )
        )

    for (aTest <- semanticTests) {
        test(aTest.name) {
            runAnalysis(aTest.expression.stripMargin) shouldBe aTest.expectedMessages.stripMargin
        }
    }

    def runAnalysis(expression : String) : String = {
        val messages =
            driver.makeast(StringSource(expression), config) match {
                case Left(ast) =>
                    val tree = new Tree[ASTNode, Program](ast)
                    val analyser = new SemanticAnalyser(tree)
                    analyser.errors
                case Right(messages) =>
                    messages
            }
        driver.messaging.formatMessages(messages)
    }

    // Subtyping

    {
        import org.bitbucket.inkytonik.cooma.SemanticAnalysis.{subtype, subtypes}
        import org.bitbucket.inkytonik.kiama.util.Positions

        def parseType(s : String) : Expression = {
            val source = new StringSource(s)
            val positions = new Positions
            val p = new CoomaParser(source, positions)
            val pr = p.pExpression(0)
            if (pr.hasValue)
                p.value(pr).asInstanceOf[Expression]
            else
                fail(p.formatParseError(pr.parseError, false))
        }

        def parseTypes(ss : Vector[String]) : Vector[Expression] =
            ss.map(parseType)

        // NOTE: these must be designed to not be sub-types of each other

        val reflSubtypeTests =
            Vector(
                "Int",
                "Str",
                "foo",
                "{x : Int}",
                "{a : Int, b : String}",
                "{r : Int, s : { a : Int, b : String}}",
                "() => Int",
                "(Int) => Int",
                "(String, Int) => String",
                "(Unit) => Int",
                "(String) => Unit",
                "({x : Int}) => String",
                "(Int) => {x : Int}",
                "((Int) => Int) => Int",
                "(Int) => (Int) => Int"
            )

        for (tt <- reflSubtypeTests) {
            test(s"reflexive subtype $tt") {
                val t = parseType(tt)
                subtype(t, t) shouldBe true
            }
        }

        for (tt <- reflSubtypeTests) {
            val t = parseType(tt)
            for (uu <- reflSubtypeTests) {
                if (tt != uu) {
                    val u = parseType(uu)
                    test(s"subtype $tt not <: $uu") {
                        subtype(t, u) shouldBe false
                    }
                }
            }
        }

        val onewaySubtypeTests =
            Vector(
                ("{x : Int, y : Int}", "{x : Int}"),
                ("{x : Int, y : Int}", "{y : Int}"),
                (
                    "({x : Int}, {y : String}) => Int",
                    "({x : Int}, {x : Int, y : String}) => Int"
                ),
                ("(Int) => {x : Int, y : Int}", "(Int) => {x : Int}")
            )

        for ((tt, uu) <- onewaySubtypeTests) {
            val t = parseType(tt)
            val u = parseType(uu)
            test(s"subtype $tt <: $uu") {
                subtype(t, u) shouldBe true
            }
            test(s"subtype $uu not <: $tt") {
                subtype(u, t) shouldBe false
            }
        }

        val twowaySubtypeTests =
            Vector(
                ("{x : Int, y : String}", "{y : String, x : Int}"),
                ("{x : Int, w : Int, y : String}", "{w : Int, x : Int, y : String}")
            )

        for ((tt, uu) <- twowaySubtypeTests) {
            val t = parseType(tt)
            val u = parseType(uu)
            test(s"subtype $tt <: $uu") {
                subtype(t, u) shouldBe true
            }
            test(s"subtype $uu <: $tt") {
                subtype(u, t) shouldBe true
            }
        }

        test("multiple subtypes (refl)") {
            val ts = parseTypes(reflSubtypeTests)
            subtypes(ts, ts) shouldBe true
        }

        test("multiple subtypes (one way)") {
            val ts = parseTypes(onewaySubtypeTests.map(_._1))
            val us = parseTypes(onewaySubtypeTests.map(_._2))
            subtypes(ts, us) shouldBe true
        }

        test("multiple subtypes (two way)") {
            val ts = parseTypes(twowaySubtypeTests.map(_._1))
            val us = parseTypes(twowaySubtypeTests.map(_._2))
            subtypes(ts, us) shouldBe true
            subtypes(us, ts) shouldBe true
        }

        test("multiple all not subtype") {
            val ts = parseTypes(Vector("Int", "String"))
            val us = parseTypes(Vector("String", "Int"))
            subtypes(ts, us) shouldBe false
            subtypes(us, ts) shouldBe false
        }

        test("multiple some not subtype") {
            val ts = parseTypes(Vector("Int", "String", "Int"))
            val us = parseTypes(Vector("Int", "Int", "Int"))
            subtypes(ts, us) shouldBe false
            subtypes(us, ts) shouldBe false
        }
    }
}
