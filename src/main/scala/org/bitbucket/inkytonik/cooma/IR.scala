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

sealed abstract class Value
case class AndV(l : String, r : String) extends Value
case class ArgV(i : Int) extends Value
case class CapV(c : String, x : String) extends Value
case class FunV(f : String, k : String, body : Term) extends Value
case class IntV(i : Int) extends Value
case class PrmV(p : String, xs : Vector[String]) extends Value
case class RowV(fs : Vector[FieldValue]) extends Value
case class SelV(r : String, f : String) extends Value
case class StrV(s : String) extends Value

case class FieldValue(f : String, x : String)

sealed abstract class Term
case class AppC(k : String, x : String) extends Term
case class AppF(f : String, k : String, x : String) extends Term
case class Halt(x : String) extends Term
case class LetC(k : String, x : String, t : Term, body : Term) extends Term
case class LetF(ds : Vector[DefTerm], body : Term) extends Term
case class LetV(x : String, v : Value, body : Term) extends Term

case class DefTerm(f : String, k : String, x : String, body : Term)

object IR {

    import org.bitbucket.inkytonik.cooma.Util.escape
    import org.bitbucket.inkytonik.kiama.output.PrettyPrinter._
    import org.bitbucket.inkytonik.kiama.output.PrettyPrinterTypes.{Document, Width}

    /*
     * Custom IR pretty-printer that escapes string terms.
     */
    def showTerm(t : Term, w : Width = defaultWidth) : String =
        formatTerm(t, w).layout

    def formatTerm(t : Term, w : Width = defaultWidth) : Document =
        pretty(group(toDocTerm(t)), w)

    def toDocTerm(t : Term) : Doc =
        t match {
            case AppC(k, x) =>
                k <+> x
            case AppF(f, k, x) =>
                f <+> k <+> x
            case Halt(x) =>
                "halt" <+> text(x)
            case LetC(k, x, t, body) =>
                "letc" <+> value(k) <+> value(x) <+> "=" <+> align(toDocTerm(t)) <@>
                    toDocTerm(body)
            case v @ LetF(ds, body) =>
                "letf" <> nest(ssep(ds.map(toDocDefTerm), emptyDoc)) <@>
                    toDocTerm(body)
            case LetV(x, v, body) =>
                "letv" <+> value(x) <+> "=" <+> align(toDocValue(v)) <@>
                    toDocTerm(body)
        }

    def toDocDefTerm(v : DefTerm) : Doc =
        line <> value(v.f) <+> value(v.k) <+> value(v.x) <+> text("=") <+> toDocTerm(v.body)

    def toDocValue(v : Value) : Doc =
        v match {
            case AndV(l, r) =>
                l <+> "&" <+> r
            case ArgV(i) =>
                "argv" <+> value(i)
            case CapV(c, x) =>
                "cap" <+> c <+> x
            case FunV(v1, v2, v3) =>
                "fun" <+> value(v1) <+> value(v2) <+> text("=>") <+> align(toDocTerm(v3))
            case IntV(i) =>
                value(i)
            case PrmV(p, xs) =>
                "prm" <+> p <+> ssep(xs.map(text), space)
            case RowV(fs) =>
                "{" <> ssep(fs.map(toDocFieldValue), "," <> space) <> text("}")
            case SelV(r, f) =>
                r <> "." <> f
            case StrV(v1) =>
                "\"" <> value(escape(v1)) <> text("\"")
        }

    def toDocFieldValue(field : FieldValue) : Doc =
        value(field.f) <+> text("=") <+> value(field.x)

}