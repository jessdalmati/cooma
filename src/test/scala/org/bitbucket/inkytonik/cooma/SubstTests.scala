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

class SubstTests extends Tests {

    import org.bitbucket.inkytonik.cooma.CoomaParserSyntax._
    import org.bitbucket.inkytonik.cooma.SymbolTable._
    import org.bitbucket.inkytonik.cooma.SemanticAnalyser
    import org.bitbucket.inkytonik.kiama.util.Messaging._
    import org.bitbucket.inkytonik.kiama.util.StringSource
    import org.bitbucket.inkytonik.kiama.rewriting.Rewriter._
    import org.bitbucket.inkytonik.kiama.relation.Tree

    val driver = new ReferenceDriver
    val config = {
        val newConfig = driver.createConfig(Seq())
        newConfig.verify()
        newConfig
    }

    case class SubstTest(
        name : String,
        program : String,
        bind : (String, String),
        expected : String
    )

    val substTests = Vector(
        SubstTest("simple: bind", "{x}", ("y", "x"), "{y}"),
        SubstTest("simple: no bind", "{x}", ("a", "b"), "{x}"),
        SubstTest(
            "simple: already defined",
            """{
              |  val x = 5
              |  x
              |}""",
            ("y", "x"),
            """{
              |  val x = 5
              |  x
              |}"""
        ),
        SubstTest(
            "blockDef: function defined",
            """{
              |   def f (x : Int) Int = x
              |   def g (y : Int) Int = f(y)
              |   g(10)
              |}""",
            ("h", "g"),
            """{
              |   def f (x : Int) Int = x
              |   def g (y : Int) Int = f(y)
              |   g(10)
              |}"""
        ),
        SubstTest(
            "blockDef: function undefined",
            """{
              |   def f (x : Int) Int = x
              |   g(10)
              |}""",
            ("h", "g"),
            """{
              |   def f (x : Int) Int = x
              |   h(10)
              |}"""
        ),
        SubstTest(
            "blockDef: function undefined, no bind",
            """{
              |   def f (x : Int) Int = x
              |   g(10)
              |}""",
            ("h", "x"),
            """{
              |   def f (x : Int) Int = x
              |   g(10)
              |}"""
        ),
        SubstTest(
            "input binding: inputs undefined",
            """{
              |   def f (b : Boolean) Int =
              |     b match {
              |       case False(_) => 1
              |       case True(_) => 2
              |     }
              |  { a = f(x), b = f(x) }
              |}""",
            ("v", "x"),
            """{
              |   def f (b : Boolean) Int =
              |     b match {
              |       case False(_) => 1
              |       case True(_) => 2
              |     }
              |  { a = f(v), b = f(v) }
              |}"""
        ),
        SubstTest(
            "input binding: inputs undefined, no bind",
            """{
              |   def f (b : Boolean) Int =
              |     b match {
              |       case False(_) => 1
              |       case True(_) => 2
              |     }
              |  { a = f(x), b = f(x) }
              |}""",
            ("v", "a"),
            """{
              |   def f (b : Boolean) Int =
              |     b match {
              |       case False(_) => 1
              |       case True(_) => 2
              |     }
              |  { a = f(x), b = f(x) }
              |}"""
        ),
        SubstTest(
            "boolean match: function with undefined variable",
            """{
              |   def f (b : Boolean) Int =
              |     b match {
              |       case False(_) => x
              |       case True(_) => 2
              |     }
              |  { a = f(false), b = f(false) }
              |}""",
            ("v", "x"),
            """{
              |   def f (b : Boolean) Int =
              |     b match {
              |       case False(_) => v
              |       case True(_) => 2
              |     }
              |  { a = f(false), b = f(false) }
              |}"""
        ),
        SubstTest(
            "boolean match: function with undefined variable, no bind",
            """{
              |   def f (b : Boolean) Int =
              |     b match {
              |       case False(_) => x
              |       case True(_) => 2
              |     }
              |  { a = f(false), b = f(false) }
              |}""",
            ("v", "spaghetti"),
            """{
              |   def f (b : Boolean) Int =
              |     b match {
              |       case False(_) => x
              |       case True(_) => 2
              |     }
              |  { a = f(false), b = f(false) }
              |}"""
        ),
        SubstTest(
            "boolean match: undefined variable",
            """{
              |   true match {
              |     case False(_) => x
              |     case True(_) => 2
              |   }
              |}""",
            ("v", "x"),
            """{
              |   true match {
              |     case False(_) => v
              |     case True(_) => 2
              |   }
              |}"""
        ),
        SubstTest(
            "multi boolean match: undefined variable",
            """{
              |   true, false match {
              |     case False(_), _ => x
              |     case True(_), _ => 2
              |   }
              |}""",
            ("v", "x"),
            """{
              |   true, false match {
              |     case False(_), _ => v
              |     case True(_), _ => 2
              |   }
              |}"""
        ),
        SubstTest(
            "multi boolean match: undefined variable, no bind",
            """{
              |   true, false match {
              |     case False(_), _ => x
              |     case True(_), _ => 2
              |   }
              |}""",
            ("v", "b"),
            """{
              |   true, false match {
              |     case False(_), _ => x
              |     case True(_), _ => 2
              |   }
              |}"""
        ),
        SubstTest(
            "record concat: already defined",
            """{
              |   val r = {x = 10, y = 20}
              |   val s = {a = "Hi"}
              |   {r & s}.x
              |}""",
            ("v", "s"),
            """{
              |   val r = {x = 10, y = 20}
              |   val s = {a = "Hi"}
              |   {r & s}.x
              |}"""
        ),
        SubstTest(
            "record concat: undefined",
            """{
              |   val r = {x = 10, y = 20}
              |   {r & s}.x
              |}""",
            ("v", "s"),
            """{
              |   val r = {x = 10, y = 20}
              |   {r & v}.x
              |}"""
        ),
        SubstTest(
            "type param: already defined",
            """{
              |   val id = fun (t : Type, x : t) x
              |   {i = id(Int, 10), s = id(String, "hello")}
              |}""",
            ("v", "t"),
            """{
              |   val id = fun (t : Type, x : t) x
              |   {i = id(Int, 10), s = id(String, "hello")}
              |}"""
        ),
        SubstTest(
            "type param: undefined",
            """{
              |   val id = fun (t : Type, x : g) x
              |   {i = id(Int, 10), s = id(String, "hello")}
              |}""",
            ("v", "g"),
            """{
              |   val id = fun (t : Type, x : v) x
              |   {i = id(Int, 10), s = id(String, "hello")}
              |}"""
        ),
        SubstTest(
            "record field",
            """{
              |   val id = fun (t : Type, x : t) x
              |   {i = id(Int, 10), s = id(String, "hello")}
              |}""",
            ("v", "i"),
            """{
              |   val id = fun (t : Type, x : t) x
              |   {i = id(Int, 10), s = id(String, "hello")}
              |}"""
        ),
        SubstTest(
            "record type field: undefined",
            """{
              |   type colour = {r : a, g : a, b : a}
              |   val x : colour = {r = 200, g = 150, b = 50}
              |   x
              |}""",
            ("v", "a"),
            """{
              |   type colour = {r : v, g : v, b : v}
              |   val x : colour = {r = 200, g = 150, b = 50}
              |   x
              |}"""
        ),
        SubstTest(
            "record type field: already defined",
            """{
              |   type a = {a : Int, b : Int}
              |   type colour = {r : a, g : a, b : a}
              |   val x : colour = {r = 200, g = 150, b = 50}
              |   x
              |}""",
            ("v", "a"),
            """{
              |   type a = {a : Int, b : Int}
              |   type colour = {r : a, g : a, b : a}
              |   val x : colour = {r = 200, g = 150, b = 50}
              |   x
              |}"""
        )
    )

    for (t <- substTests) {
        test(t.name) {
            getast(t.program.stripMargin, Seq()) match {
                case Left(p1) => getast(t.expected.stripMargin, Seq()) match {
                    case Left(p2) => substVar(p1, t.bind._2, t.bind._1) shouldBe p2
                    case Right(msg) => fail("Expected program failed to parse with messages: "
                        + driver.messaging.formatMessages(msg))
                }
                case Right(msg) => fail("Test program failed to parse with messages: "
                    + driver.messaging.formatMessages(msg))
            }
        }
    }

    def getast(program : String, args : Seq[String]) : Either[ASTNode, Messages] = {
        driver.makeast(StringSource(program), config)
    }

    /**
     * Substitute one variable for another where it is free
     */
    def substVar(prog : ASTNode, oldVar : String, newVar : String) : ASTNode = {
        val semanticAnalyser = new SemanticAnalyser(new Tree(prog))
        val substIdn =
            rule[ASTNode] {
                case Idn(i @ IdnUse(`oldVar`)) if semanticAnalyser.entity(i) == UnknownEntity() => Idn(IdnUse(newVar))
            }
        rewrite(everywhere(substIdn))(prog)
    }

    case class ExprSubTest(
        name : String,
        tree : Expression,
        bind : (String, String),
        expected : Expression
    )

    val exprSubTests = Vector(
        ExprSubTest(
            "simple expr sub test",
            Idn(IdnUse("a")),
            ("v1", "a"),
            Idn(IdnUse("v1"))
        )
    )

    for (t <- exprSubTests) {
        test(t.name) {
            substExpr(t.tree, t.bind._2, t.bind._1) shouldBe t.expected
        }
    }

    def substExpr(prog : Expression, oldVar : String, newVar : String) : Expression = {
        val semanticAnalyser = new SemanticAnalyser(new Tree(prog))
        val substIdn =
            rule[ASTNode] {
                case Idn(i @ IdnUse(`oldVar`)) if semanticAnalyser.entity(i) == UnknownEntity() => Idn(IdnUse(newVar))
            }
        rewrite(allbu(substIdn))(prog)
    }
}
