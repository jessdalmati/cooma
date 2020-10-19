package org.bitbucket.inkytonik.cooma

trait Compiler {

    self : Backend =>

    import org.bitbucket.inkytonik.cooma.CoomaParserPrettyPrinter.show
    import org.bitbucket.inkytonik.cooma.CoomaParserSyntax._
    import org.bitbucket.inkytonik.cooma.Primitives._
    import org.bitbucket.inkytonik.cooma.Util.{fresh, resetFresh, unescape}
    import org.bitbucket.inkytonik.kiama.rewriting.Rewriter._
    import org.bitbucket.inkytonik.kiama.relation._
    import org.bitbucket.inkytonik.cooma.SymbolTable._

    /**
     * Compile a program that will run as a command with
     * user-supplied command-line arguments.
     */
    def compileCommand(prog : Program) : Term = {
        resetFresh()
        compileTop(prog.expression, 0)
    }

    /**
     * Compile a program that is evaluated as an expression
     * with no command-line arguments.
     */
    def compileStandalone(prog : Program) : Term = {
        resetFresh()
        compileHalt(prog.expression)
    }

    /**
     * Name of capability type?
     */
    def isCapabilityName(n : String) : Boolean =
        (n == "Writer") || (n == "Reader") || (n == "ReaderWriter")

    /**
     * Case class and map that stores primitives metadata.
     */
    case class PrimitiveMeta(prm : Primitive)

    val primitivesTable = Map(
        "Equal" -> PrimitiveMeta(equalP),
        "IntAbs" -> PrimitiveMeta(intBinP(ABS)),
        "IntAdd" -> PrimitiveMeta(intBinP(ADD)),
        "IntSub" -> PrimitiveMeta(intBinP(SUB)),
        "IntMul" -> PrimitiveMeta(intBinP(MUL)),
        "IntDiv" -> PrimitiveMeta(intBinP(DIV)),
        "IntPow" -> PrimitiveMeta(intBinP(POW)),
        "IntGt" -> PrimitiveMeta(intRelP(GT)),
        "IntGte" -> PrimitiveMeta(intRelP(GTE)),
        "IntLt" -> PrimitiveMeta(intRelP(LT)),
        "IntLte" -> PrimitiveMeta(intRelP(LTE)),
        "StrConcat" -> PrimitiveMeta(stringP(CONCAT)),
        "StrLength" -> PrimitiveMeta(stringP(LENGTH)),
        "StrSubstr" -> PrimitiveMeta(stringP(SUBSTR))
    )

    /**
     * Compile an expression to produce its value via the halt
     * continuation.
     */
    def compileHalt(exp : Expression) : Term =
        compile(exp, z => appC("$halt", z))

    def compileTop(exp : Expression, nArg : Int) : Term = {

        def compileTopArg(a : String, t : Expression, e : Expression) : Term = {

            def compileCapArg(n : String) : Term = {
                val x = fresh("x")
                letV(x, prmV(argumentP(nArg), Vector()),
                    letV(a, prmV(capabilityP(n), Vector(x)),
                        compileTop(e, nArg + 1)))
            }

            t match {
                case ReaderT()       => compileCapArg("Reader")
                case ReaderWriterT() => compileCapArg("ReaderWriter")
                case WriterT()       => compileCapArg("Writer")

                case StrT() =>
                    letV(a, prmV(argumentP(nArg), Vector()),
                        compileTop(e, nArg + 1))

                case _ =>
                    sys.error(s"compileTopArg: ${show(t)} arguments not supported")
            }

        }

        exp match {
            case Fun(Arguments(Vector()), e) =>
                compileHalt(e)
            case Fun(Arguments(Vector(Argument(IdnDef(a), t, _))), e) =>
                compileTopArg(a, t, e)
            case Fun(Arguments(Argument(IdnDef(a), t, _) +: as), e) =>
                compileTopArg(a, t, Fun(Arguments(as), e))
            case _ =>
                compileHalt(exp)
        }
    }

    val and =
        Fun(
            Arguments(Vector(
                Argument(IdnDef("l"), BoolT(), None),
                Argument(IdnDef("r"), BoolT(), None)
            )),
            Mat(
                Idn(IdnUse("l")),
                Vector(),
                Vector(
                    Case(Vector(VPtrn("False", SPtrn(IdnDef("_")))), False()),
                    Case(Vector(VPtrn("True", SPtrn(IdnDef("_")))), Idn(IdnUse("r")))
                ),
                NoDflt()
            )
        )

    val not =
        Fun(
            Arguments(Vector(
                Argument(IdnDef("b"), BoolT(), None)
            )),
            Mat(
                Idn(IdnUse("b")),
                Vector(),
                Vector(
                    Case(Vector(VPtrn("False", SPtrn(IdnDef("_")))), True()),
                    Case(Vector(VPtrn("True", SPtrn(IdnDef("_")))), False())
                ),
                NoDflt()
            )
        )

    val or =
        Fun(
            Arguments(Vector(
                Argument(IdnDef("l"), BoolT(), None),
                Argument(IdnDef("r"), BoolT(), None)
            )),
            Mat(
                Idn(IdnUse("l")),
                Vector(),
                Vector(
                    Case(Vector(VPtrn("False", SPtrn(IdnDef("_")))), Idn(IdnUse("r"))),
                    Case(Vector(VPtrn("True", SPtrn(IdnDef("_")))), True())
                ),
                NoDflt()
            )
        )

    val booleans =
        Rec(Vector(
            Field("and", and),
            Field("not", not),
            Field("or", or)
        ))

    def mkPrimField(fieldName : String, argTypes : Vector[Expression], primName : String) : Field = {
        val argNames = (1 to argTypes.length).map(i => s"arg$i")
        val args = argNames.zip(argTypes).map { case (n, t) => Argument(IdnDef(n), t, None) }
        val params = argNames.map(n => Idn(IdnUse(n))).toVector
        Field(fieldName, Fun(Arguments(args.toVector), Prm(primName, params)))
    }

    def mkInt1PrimField(fieldName : String, primName : String) : Field =
        mkPrimField(fieldName, Vector(IntT()), primName)

    def mkInt2PrimField(fieldName : String, primName : String) : Field =
        mkPrimField(fieldName, Vector(IntT(), IntT()), primName)

    def mkStr1PrimField(fieldName : String, primName : String) : Field =
        mkPrimField(fieldName, Vector(StrT()), primName)

    def mkStr2PrimField(fieldName : String, primName : String) : Field =
        mkPrimField(fieldName, Vector(StrT(), StrT()), primName)

    def mkStrIntPrimField(fieldName : String, primName : String) : Field =
        mkPrimField(fieldName, Vector(StrT(), IntT()), primName)

    val equal =
        Fun(
            Arguments(Vector(
                Argument(IdnDef("t"), TypT(), None),
                Argument(IdnDef("l"), Idn(IdnUse("t")), None),
                Argument(IdnDef("r"), Idn(IdnUse("t")), None)
            )),
            Prm("Equal", Vector(
                Idn(IdnUse("t")),
                Idn(IdnUse("l")),
                Idn(IdnUse("r"))
            ))
        )

    val ints =
        Rec(Vector(
            mkInt1PrimField("abs", "IntAbs"),
            mkInt2PrimField("add", "IntAdd"),
            mkInt2PrimField("div", "IntDiv"),
            mkInt2PrimField("mul", "IntMul"),
            mkInt2PrimField("pow", "IntPow"),
            mkInt2PrimField("sub", "IntSub"),
            mkInt2PrimField("lt", "IntLt"),
            mkInt2PrimField("lte", "IntLte"),
            mkInt2PrimField("gt", "IntGt"),
            mkInt2PrimField("gte", "IntGte")
        ))

    val strings =
        Rec(Vector(
            mkStr2PrimField("concat", "StrConcat"),
            mkStr1PrimField("length", "StrLength"),
            mkStrIntPrimField("substr", "StrSubstr")
        ))

    def compile(exp : Expression, kappa : String => Term) : Term =
        exp match {
            case App(f, Vector()) =>
                compile(App(f, Vector(Uni())), kappa)

            case App(f, Vector(a)) =>
                val k = fresh("k")
                val r = fresh("r")
                compile(f, y =>
                    compile(a, z =>
                        letC(k, r, kappa(r),
                            appF(y, k, z))))

            case App(f, a +: as) =>
                compile(App(App(f, Vector(a)), as), kappa)

            case Blk(be) =>
                compileBlockExp(be, kappa)

            case Booleans() =>
                compile(booleans, kappa)

            case Cat(r1, r2) =>
                val r = fresh("r")
                compile(r1, y =>
                    compile(r2, z =>
                        letV(r, prmV(recConcatP(), Vector(y, z)),
                            kappa(r))))

            case Eql() =>
                compile(equal, kappa)

            case False() =>
                compile(Var(Field("False", Uni())), kappa)

            case Fun(Arguments(Vector()), e) =>
                compileFun("_", UniT(), e, kappa)

            case Fun(Arguments(Vector(Argument(IdnDef(x), t, _))), e) =>
                compileFun(x, t, e, kappa)

            case Fun(Arguments(Argument(IdnDef(x), t, _) +: as), e) =>
                compileFun(x, t, Fun(Arguments(as), e), kappa)

            case Idn(IdnUse(i)) =>
                kappa(i)

            case Ints() =>
                compile(ints, kappa)

            case Mat(e, es, cs, d) =>
                compileMatch(e, es, cs, d, kappa)

            case Num(n) =>
                val i = fresh("i")
                letV(i, intV(n),
                    kappa(i))

            case Prm(p, args) =>
                val r = fresh("r")
                compilePrimArgs(args, cArgs => letV(r, prmV(primitivesTable(p).prm, cArgs),
                    kappa(r)))

            case Rec(fields) =>
                val r = fresh("r")
                compileRec(fields, fvs => letV(r, recV(fvs), kappa(r)))

            case Sel(r, FieldUse(s)) =>
                val f = fresh("f")
                compile(r, z =>
                    letV(f, prmV(recSelectP(), Vector(z, s)),
                        kappa(f)))

            case Str(l) =>
                val s = fresh("s")
                letV(s, strV(unescape(l.tail.init)),
                    kappa(s))

            case Strings() =>
                compile(strings, kappa)

            case True() =>
                compile(Var(Field("True", Uni())), kappa)

            case Uni() =>
                val u = fresh("u")
                letV(u, recV(Vector()),
                    kappa(u))

            case v @ Var(field) =>
                val r = fresh("r")
                compile(field.expression, z =>
                    letV(r, varV(field.identifier, z),
                        kappa(r)))

            // Types erase to unit
            case IsType() =>
                compile(Uni(), kappa)
        }

    object IsType {
        def unapply(e : Expression) : Boolean =
            e match {
                case BoolT() | ReaderT() | ReaderWriterT() | WriterT() |
                    _ : FunT | _ : IntT | _ : RecT | _ : StrT | _ : TypT |
                    _ : UniT | _ : VarT =>
                    true
                case _ =>
                    false
            }
    }

    def compileCapFun(n : String, x : String, e : Expression, kappa : String => Term) : Term = {
        val f = fresh("f")
        val j = fresh("k")
        val y = fresh("y")
        letV(f, funV(j, y,
            letV(x, prmV(capabilityP(n), Vector(y)),
                tailCompile(e, j))),
            kappa(f))
    }

    def compileFun(x : String, t : Expression, e : Expression, kappa : String => Term) : Term = {
        val f = fresh("f")
        val j = fresh("k")
        letV(f, funV(j, x, tailCompile(e, j)),
            kappa(f))
    }

    def compileBlockExp(be : BlockExp, kappa : String => Term) : Term =
        be match {
            case BlkDef(ds, be2) =>
                letF(
                    ds.defs.map(compileDef),
                    compileBlockExp(be2, kappa)
                )

            case BlkLet(Let(_, IdnDef(x), _, e), be2) =>
                val j = fresh("k")
                letC(j, x, compileBlockExp(be2, kappa),
                    tailCompile(e, j))

            case Return(e) =>
                compile(e, kappa)
        }

    def compileDefBody(args : Vector[Argument], e : Expression, k : String) : Term =
        if (args.isEmpty)
            tailCompile(e, k)
        else
            tailCompile(Fun(Arguments(args), e), k)

    def compileDef(fd : Def) : DefTerm = {
        val k = fresh("k")
        fd match {
            case Def(IdnDef(f), Body(Arguments(Vector()), t, e)) =>
                compileDef(Def(IdnDef(f), Body(Arguments(Vector(Argument(IdnDef("_"), UniT(), None))), t, e)))

            case Def(IdnDef(f), Body(Arguments(Argument(IdnDef(x), _, None) +: otherArgs), _, e)) =>
                defTerm(f, k, x, compileDefBody(otherArgs, e, k))
        }
    }

    def substVar(exp : Expression, oldVar : String, newVar : String) : Expression = {
        val prog = Program(exp)
        val semanticAnalyser = new SemanticAnalyser(new Tree(prog))
        val substIdn =
            rule[ASTNode] {
                case Idn(i @ IdnUse(`oldVar`)) if semanticAnalyser.entity(i) == UnknownEntity() => Idn(IdnUse(newVar))
            }
        rewrite(everywhere(substIdn))(prog) match {
            case Program(e) => e
        }
    }

    def newRec(exp : Expression, cons : Vector[String]) : Expression = {
        Rec(cons.map(c => Field(c, Sel(exp, FieldUse(c)))))
    }

    def compileCase_2(e : Expression, es : Vector[Expression],
        css : Vector[Case], d : Default, kappa : String => Term) : Term = {

        val dk = fresh("k")

        val vi = fresh("v")

        val cks = es match {
            case h +: t =>
                ((SPtrn(IdnDef(vi)), Mat(h, t, css.map {
                    case Case(SPtrn(IdnDef(idn)) +: t, e) =>
                        Case(t, substVar(e, idn, vi))
                }, d)), fresh("k"))
            case _ => css(0) match {
                case Case(p +: _, expr) =>
                    ((p, expr), fresh("k"))
            }
        }

        val caseTerms = cks match {
            case (_, k) => Vector(sCaseTerm(k))
        }

        compile(e, z =>
            cks match {
                case ((SPtrn(IdnDef(xi)), ei), ki) =>
                    letC(ki, xi, compile(ei, zi => kappa(zi)),
                        letC(dk, z, compileHalt(Num(-1)),
                            casV(z, caseTerms, dk)))
            })
    }

    def compileCase_3(e : Expression, es : Vector[Expression], css : Vector[Case],
        d : Default, kappa : String => Term) : Term = {

        //stable sort
        //map of constructor type to cases with the first pattern of that type
        val grouped = css.groupBy {
            case Case(VPtrn(cons, _) +: t, _) => cons
        }

        //new constructor cases with fresh variables
        //with expressions that are matches with cases with
        //first pattern removed and also subpatterns placed at the head
        val newCases = grouped.map {
            case (cons, cs) => {
                val vi = fresh("v")
                Case(
                    Vector(VPtrn(cons, SPtrn(IdnDef(vi)))),
                    Mat(
                        Idn(IdnUse(vi)),
                        es,
                        cs.map {
                            case Case(VPtrn(_, sp) +: t, expr) =>
                                Case(sp +: t, expr)
                        },
                        d
                    )
                )
            }
        }

        val dk = fresh("k")

        val cks = newCases.map(c => (c, fresh("k")))

        val caseTerms = cks.map {
            case (Case(VPtrn(idn, _) +: t, _), k) => vCaseTerm(idn, k)
        }.toVector

        compile(e, z => cks.foldLeft(letC(dk, z, d match {
            case Dflt(d)  => compile(d, zi => kappa(zi))
            case NoDflt() => compileHalt(Num(-1))
        }, casV(z, caseTerms, dk))) {
            case (t, (Case(VPtrn(_, SPtrn(IdnDef(xi))) +: _, ei), ki)) =>
                letC(ki, xi, compile(ei, zi => kappa(zi)), t)
        })

    }

    def compileCaseInt(e : Expression, es : Vector[Expression], css : Vector[Case],
        d : Default, kappa : String => Term) : Term = {

        val grouped = css.groupBy {
            case Case(IPtrn(n) +: _, _) => n
        }

        val newCases = grouped.map {
            case (cons, cs) => es match {
                case h +: t =>
                    Case(
                        Vector(IPtrn(cons)),
                        Mat(h, t, cs.map {
                            case Case(IPtrn(_) +: t, expr) =>
                                Case(t, expr)
                        }, d)
                    )
                case _ => cs(0)
            }
        }

        val dk = fresh("k")

        val cks = newCases.map(c => (c, fresh("k")))

        val caseTerms = cks.map {
            case (Case(IPtrn(n) +: _, _), k) => iCaseTerm(n, k)
        }.toVector

        compile(e, z => cks.foldLeft(letC(dk, z, d match {
            case Dflt(d)  => compile(d, zi => kappa(zi))
            case NoDflt() => compileHalt(Num(-1))
        }, casV(z, caseTerms, dk))) {
            case (t, (Case(IPtrn(n) +: _, ei), ki)) =>
                letC(ki, fresh("v"), compile(ei, zi => kappa(zi)), t)
        })
    }

    def compileCaseStr(e : Expression, es : Vector[Expression], css : Vector[Case],
        d : Default, kappa : String => Term) : Term = {

        val grouped = css.groupBy {
            case Case(StrPtrn(str) +: _, _) => str
        }

        val newCases = grouped.map {
            case (cons, cs) => es match {
                case h +: t =>
                    Case(
                        Vector(StrPtrn(cons)),
                        Mat(h, t, cs.map {
                            case Case(StrPtrn(_) +: t, expr) =>
                                Case(t, expr)
                        }, d)
                    )
                case _ => cs(0)
            }
        }

        val dk = fresh("k")

        val cks = newCases.map(c => (c, fresh("k")))

        val caseTerms = cks.map {
            case (Case(StrPtrn(str) +: _, _), k) => strCaseTerm(str, k)
        }.toVector

        compile(e, z => cks.foldLeft(letC(dk, z, d match {
            case Dflt(d)  => compile(d, zi => kappa(zi))
            case NoDflt() => compileHalt(Num(-1))
        }, casV(z, caseTerms, dk))) {
            case (t, (Case(StrPtrn(str) +: _, ei), ki)) =>
                letC(ki, fresh("v"), compile(ei, zi => kappa(zi)), t)
        })
    }

    def compileCaseRec(e : Expression, es : Vector[Expression], css : Vector[Case],
        d : Default, kappa : String => Term) : Term = {

        //stable sort
        //map of constructor type to cases with the first pattern of that type
        val grouped = css.groupBy {
            case Case(RPtrnLit(p, ps) +: _, _) => (p match {
                case FPtrn(lb, _) => lb
                case LPtrn(lb)    => lb
            }) +: ps.map {
                case FPtrn(lb, _) => lb
                case LPtrn(lb)    => lb
            }
            case Case(RPtrnCons(p, ps, _) +: _, _) => (p match {
                case FPtrn(lb, _) => lb
                case LPtrn(lb)    => lb
            }) +: ps.map {
                case FPtrn(lb, _) => lb
                case LPtrn(lb)    => lb
            }
            case Case(RPtrnE() +: _, _) => Vector()
        }

        //new constructor cases with fresh variables
        //with expressions that are matches with cases with
        //first pattern removed and also subpatterns placed at the head
        val newCases = grouped.map {
            case (cons +: t, cs) => {
                Case(
                    Vector(RPtrnLit(FPtrn(cons, SPtrn(IdnDef(cons))), Vector())),
                    Mat(
                        //newRec(e, t), 
                        e, Idn(IdnUse(cons)) +: es,
                        cs.map {
                            case Case(RPtrnLit(p, ps) +: t, expr) => ps match {
                                case f +: fs => p match {
                                    case FPtrn(_, sp) => Case(RPtrnLit(f, fs) +: sp +: t, expr)
                                    case LPtrn(cons)  => Case(RPtrnLit(f, fs) +: SPtrn(IdnDef(cons)) +: t, expr)
                                }
                                case _ => p match {
                                    case FPtrn(_, sp) => Case(RPtrnE() +: sp +: t, expr)
                                    case LPtrn(cons)  => Case(RPtrnE() +: SPtrn(IdnDef(cons)) +: t, expr)
                                }
                            }
                            case Case(RPtrnCons(p, ps, idn) +: t, expr) => ps match {
                                case f +: fs => p match {
                                    case FPtrn(_, sp) => Case(RPtrnCons(f, fs, idn) +: sp +: t, expr)
                                    case LPtrn(cons)  => Case(RPtrnCons(f, fs, idn) +: SPtrn(IdnDef(cons)) +: t, expr)
                                }
                                case _ => p match {
                                    case FPtrn(_, sp) => Case(SPtrn(idn) +: sp +: t, expr)
                                    case LPtrn(cons)  => Case(SPtrn(idn) +: SPtrn(IdnDef(cons)) +: t, expr)
                                }
                            }
                        },
                        d
                    )
                )
            }
            case (_, cs) => {
                es match {
                    case h +: t => Case(
                        Vector(RPtrnE()),
                        Mat(
                            h, t,
                            cs.map {
                                case Case(RPtrnE() +: t, expr) =>
                                    Case(t, expr)
                            },
                            d
                        )
                    )
                    case _ => cs(0)
                }
            }
        }

        val dk = fresh("k")

        val cks = newCases.map(c => (c, fresh("k")))

        val caseTerms = cks.map {
            case (Case(RPtrnLit(FPtrn(name, _), _) +: _, _), k) => rCaseTerm(name, k)
            case (Case(RPtrnE() +: _, _), k)                    => eCaseTerm(k)
        }.toVector

        compile(e, z => cks.foldLeft(letC(dk, z, d match {
            case Dflt(d)  => compile(d, zi => kappa(zi))
            case NoDflt() => compileHalt(Num(-1))
        }, casV(z, caseTerms, dk))) {
            case (t, (Case(RPtrnLit(FPtrn(_, SPtrn(IdnDef(xi))), _) +: _, ei), ki)) =>
                letC(ki, xi, compile(ei, zi => kappa(zi)), t)
            case (t, (Case(RPtrnE() +: _, ei), ki)) =>
                letC(ki, fresh("v"), compile(ei, zi => kappa(zi)), t)
        })

    }

    def compileMatch(e : Expression, es : Vector[Expression], cs : Vector[Case], d : Default, kappa : String => Term) : Term = {
        //cases before the split
        val css = cs match {
            case Case(SPtrn(_) +: t, _) +: tail => cs.takeWhile {
                case Case(SPtrn(_) +: t, _) => true
                case _                      => false
            }
            case _ => cs.takeWhile {
                case Case(SPtrn(_) +: t, _) => false
                case _                      => true
            }
        }

        //rest of the cases after the split
        val rest = css match {
            case Case(SPtrn(_) +: t, _) +: tail => cs.dropWhile {
                case Case(SPtrn(_) +: t, _) => true
                case _                      => false
            }
            case _ => cs.dropWhile {
                case Case(SPtrn(_) +: t, _) => false
                case _                      => true
            }
        }

        //default with the rest of the cases
        //(major tree explosion ?)
        val nd = rest match {
            case h +: t => Dflt(Mat(e, es, rest, d))
            case _      => d
        }

        //determining to compile with case2 or case3
        css match {
            case Case(SPtrn(_) +: _, _) +: _ =>
                compileCase_2(e, es, css, nd, kappa)
            case Case(VPtrn(_, _) +: _, _) +: _ =>
                compileCase_3(e, es, css, nd, kappa)
            case Case(r @ (RPtrnLit(_, _) | RPtrnCons(_, _, _) | RPtrnE()) +: _, _) +: _ =>
                compileCaseRec(e, es, css, nd, kappa)
            case Case(IPtrn(_) +: _, _) +: _ =>
                compileCaseInt(e, es, css, nd, kappa)
            case Case(StrPtrn(_) +: _, _) +: _ =>
                compileCaseStr(e, es, css, nd, kappa)
        }
    }

    def compileRec(
        fields : Vector[Field],
        kappa : Vector[FieldValue] => Term
    ) : Term =
        fields match {
            case Field(f, e) +: t =>
                compile(e, z =>
                    compileRec(t, fvs => kappa(fieldValue(f, z) +: fvs)))

            case Vector() =>
                kappa(Vector())
        }

    def compilePrimArgs(
        args : Vector[Expression],
        kappa : Vector[String] => Term
    ) : Term =
        args match {
            case e +: t =>
                compile(e, argE =>
                    compilePrimArgs(t, argT => kappa(argE +: argT)))

            case Vector() =>
                kappa(Vector())
        }

    def tailCompile(exp : Expression, k : String) : Term =
        exp match {
            case App(f, Vector()) =>
                tailCompile(App(f, Vector(Uni())), k)

            case App(f, Vector(a)) =>
                compile(f, y =>
                    compile(a, z =>
                        appF(y, k, z)))

            case App(f, a +: as) =>
                tailCompile(App(App(f, Vector(a)), as), k)

            case Blk(be) =>
                tailCompileBlockExp(be, k)

            case Booleans() =>
                tailCompile(booleans, k)

            case Cat(r1, r2) =>
                val r = fresh("r")
                compile(r1, y =>
                    compile(r2, z =>
                        letV(r, prmV(recConcatP(), Vector(y, z)),
                            appC(k, r))))

            case Eql() =>
                tailCompile(equal, k)

            case False() =>
                tailCompile(Var(Field("False", Uni())), k)

            case Fun(Arguments(Vector()), e) =>
                tailCompileFun("_", UniT(), e, k)

            case Fun(Arguments(Vector(Argument(IdnDef(x), t, _))), e) =>
                tailCompileFun(x, t, e, k)

            case Fun(Arguments(Argument(IdnDef(x), t, _) +: as), e) =>
                tailCompileFun(x, t, Fun(Arguments(as), e), k)

            case Fun(Arguments(a +: as), e) =>
                tailCompile(Fun(Arguments(Vector(a)), Fun(Arguments(as), e)), k)

            case Idn(IdnUse(x)) =>
                appC(k, x)

            case Ints() =>
                tailCompile(ints, k)

            case Mat(e, es, cs, d) =>
                tailCompileMatch(e, es, cs, d, k)

            case Num(n) =>
                val i = fresh("i")
                letV(i, intV(n),
                    appC(k, i))

            case Prm(p, args) =>
                val r = fresh("r")
                compilePrimArgs(args, cArgs =>
                    letV(r, prmV(primitivesTable(p).prm, cArgs),
                        appC(k, r)))

            case Rec(fields) =>
                val r = fresh("r")
                compileRec(fields, fvs => letV(r, recV(fvs), appC(k, r)))

            case Sel(r, FieldUse(s)) =>
                val f = fresh("f")
                compile(r, z =>
                    letV(f, prmV(recSelectP(), Vector(z, s)),
                        appC(k, f)))

            case Str(l) =>
                val s = fresh("s")
                letV(s, strV(unescape(l.tail.init)),
                    appC(k, s))

            case Strings() =>
                tailCompile(strings, k)

            case True() =>
                tailCompile(Var(Field("True", Uni())), k)

            case Uni() =>
                val u = fresh("u")
                letV(u, recV(Vector()),
                    appC(k, u))

            case Var(field) =>
                val r = fresh("r")
                compile(field.expression, z =>
                    letV(r, varV(field.identifier, z),
                        appC(k, r)))

            // Types erase to unit
            case IsType() =>
                tailCompile(Uni(), k)
        }

    def tailCompileCapFun(n : String, x : String, e : Expression, k : String) : Term = {
        val f = fresh("f")
        val j = fresh("k")
        val y = fresh("y")
        letV(f, funV(j, y,
            letV(x, prmV(capabilityP(n), Vector(y)),
                tailCompile(e, j))),
            appC(k, x))
    }

    def tailCompileFun(x : String, t : Expression, e : Expression, k : String) : Term = {
        val f = fresh("f")
        val j = fresh("k")
        letV(f, funV(j, x, tailCompile(e, j)),
            appC(k, f))
    }

    def tailCompileBlockExp(be : BlockExp, k : String) : Term =
        be match {
            case BlkDef(ds, be2) =>
                letF(
                    ds.defs.map(compileDef),
                    tailCompileBlockExp(be2, k)
                )

            case BlkLet(Let(_, IdnDef(x), _, e), be2) =>
                val j = fresh("k")
                letC(j, x, tailCompileBlockExp(be2, k),
                    tailCompile(e, j))

            case Return(e) =>
                tailCompile(e, k)
        }

    def tailCompileCase_2(e : Expression, es : Vector[Expression],
        css : Vector[Case], d : Default, k : String) : Term = {

        val dk = fresh("k")

        val vi = fresh("v")

        val cks = es match {
            case h +: t =>
                ((SPtrn(IdnDef(vi)), Mat(h, t, css.map {
                    case Case(SPtrn(IdnDef(idn)) +: t, e) =>
                        Case(t, substVar(e, idn, vi))
                }, d)), fresh("k"))
            case _ => css(0) match {
                case Case(p +: _, expr) =>
                    ((p, expr), fresh("k"))
            }
        }

        val caseTerms = cks match {
            case (_, k) => Vector(sCaseTerm(k))
        }

        compile(e, z =>
            cks match {
                case ((SPtrn(IdnDef(xi)), ei), ki) =>
                    letC(ki, xi, tailCompile(ei, k),
                        letC(dk, z, compileHalt(Num(-1)),
                            casV(z, caseTerms, dk)))
            })
    }

    def tailCompileCase_3(e : Expression, es : Vector[Expression], css : Vector[Case],
        d : Default, k : String) : Term = {

        //stable sort
        //map of constructor type to cases with the first pattern of that type
        val grouped = css.groupBy {
            case Case(VPtrn(cons, _) +: t, _) => cons
        }

        //new constructor cases with fresh variables
        //with expressions that are matches with cases with
        //first pattern removed and also subpatterns placed at the head
        val newCases = grouped.map {
            case (cons, cs) => {
                val vi = fresh("v")
                Case(
                    Vector(VPtrn(cons, SPtrn(IdnDef(vi)))),
                    Mat(
                        Idn(IdnUse(vi)),
                        es,
                        cs.map {
                            case Case(VPtrn(_, sp) +: t, expr) =>
                                Case(sp +: t, expr)
                        },
                        d
                    )
                )
            }
        }

        val dk = fresh("k")

        val cks = newCases.map(c => (c, fresh("k")))

        val caseTerms = cks.map {
            case (Case(VPtrn(idn, _) +: t, _), k) => vCaseTerm(idn, k)
        }.toVector

        compile(e, z => cks.foldLeft(letC(dk, z, d match {
            case Dflt(d)  => tailCompile(d, k)
            case NoDflt() => compileHalt(Num(-1))
        }, casV(z, caseTerms, dk))) {
            case (t, (Case(VPtrn(_, SPtrn(IdnDef(xi))) +: _, ei), ki)) =>
                letC(ki, xi, tailCompile(ei, k), t)
        })

    }

    def tailCompileCaseRec(e : Expression, es : Vector[Expression], css : Vector[Case],
        d : Default, k : String) : Term = {

        //stable sort
        //map of constructor type to cases with the first pattern of that type
        val grouped = css.groupBy {
            case Case(RPtrnLit(p, ps) +: _, _) => (p match {
                case FPtrn(lb, _) => lb
                case LPtrn(lb)    => lb
            }) +: ps.map {
                case FPtrn(lb, _) => lb
                case LPtrn(lb)    => lb
            }
            case Case(RPtrnCons(p, ps, _) +: _, _) => (p match {
                case FPtrn(lb, _) => lb
                case LPtrn(lb)    => lb
            }) +: ps.map {
                case FPtrn(lb, _) => lb
                case LPtrn(lb)    => lb
            }
            case Case(RPtrnE() +: _, _) => Vector()
        }

        //new constructor cases with fresh variables
        //with expressions that are matches with cases with
        //first pattern removed and also subpatterns placed at the head
        val newCases = grouped.map {
            case (cons +: t, cs) => {
                Case(
                    Vector(RPtrnLit(FPtrn(cons, SPtrn(IdnDef(cons))), Vector())),
                    Mat(
                        newRec(e, t), Idn(IdnUse(cons)) +: es,
                        cs.map {
                            case Case(RPtrnLit(p, ps) +: t, expr) => ps match {
                                case f +: fs => p match {
                                    case FPtrn(_, sp) => Case(RPtrnLit(f, fs) +: sp +: t, expr)
                                    case LPtrn(cons)  => Case(RPtrnLit(f, fs) +: SPtrn(IdnDef(cons)) +: t, expr)
                                }
                                case _ => p match {
                                    case FPtrn(_, sp) => Case(RPtrnE() +: sp +: t, expr)
                                    case LPtrn(cons)  => Case(RPtrnE() +: SPtrn(IdnDef(cons)) +: t, expr)
                                }
                            }
                            case Case(RPtrnCons(p, ps, idn) +: t, expr) => ps match {
                                case f +: fs => p match {
                                    case FPtrn(_, sp) => Case(RPtrnCons(f, fs, idn) +: sp +: t, expr)
                                    case LPtrn(cons)  => Case(RPtrnCons(f, fs, idn) +: SPtrn(IdnDef(cons)) +: t, expr)
                                }
                                case _ => p match {
                                    case FPtrn(_, sp) => Case(SPtrn(idn) +: sp +: t, expr)
                                    case LPtrn(cons)  => Case(SPtrn(idn) +: SPtrn(IdnDef(cons)) +: t, expr)
                                }
                            }
                        },
                        d
                    )
                )
            }
            case (_, cs) => {
                es match {
                    case h +: t => Case(
                        Vector(RPtrnE()),
                        Mat(
                            h, t,
                            cs.map {
                                case Case(RPtrnE() +: t, expr) =>
                                    Case(t, expr)
                            },
                            d
                        )
                    )
                    case _ => cs(0)
                }
            }
        }

        val dk = fresh("k")

        val cks = newCases.map(c => (c, fresh("k")))

        val caseTerms = cks.map {
            case (Case(RPtrnLit(FPtrn(name, _), _) +: _, _), k) => rCaseTerm(name, k)
            case (Case(RPtrnE() +: _, _), k)                    => eCaseTerm(k)
        }.toVector

        compile(e, z => cks.foldLeft(letC(dk, z, d match {
            case Dflt(d)  => tailCompile(d, k)
            case NoDflt() => compileHalt(Num(-1))
        }, casV(z, caseTerms, dk))) {
            case (t, (Case(RPtrnLit(FPtrn(_, SPtrn(IdnDef(xi))), _) +: _, ei), ki)) =>
                letC(ki, xi, tailCompile(ei, k), t)
            case (t, (Case(RPtrnE() +: _, ei), ki)) =>
                letC(ki, fresh("v"), tailCompile(ei, k), t)
        })

    }

    def tailCompileCaseInt(e : Expression, es : Vector[Expression], css : Vector[Case],
        d : Default, k : String) : Term = {

        val grouped = css.groupBy {
            case Case(IPtrn(n) +: _, _) => n
        }

        val newCases = grouped.map {
            case (cons, cs) => es match {
                case h +: t =>
                    Case(
                        Vector(IPtrn(cons)),
                        Mat(h, t, cs.map {
                            case Case(IPtrn(_) +: t, expr) =>
                                Case(t, expr)
                        }, d)
                    )
                case _ => cs(0)
            }
        }

        val dk = fresh("k")

        val cks = newCases.map(c => (c, fresh("k")))

        val caseTerms = cks.map {
            case (Case(IPtrn(n) +: _, _), k) => iCaseTerm(n, k)
        }.toVector

        compile(e, z => cks.foldLeft(letC(dk, z, d match {
            case Dflt(d)  => tailCompile(d, k)
            case NoDflt() => compileHalt(Num(-1))
        }, casV(z, caseTerms, dk))) {
            case (t, (Case(IPtrn(n) +: _, ei), ki)) =>
                letC(ki, fresh("v"), tailCompile(ei, k), t)
        })
    }

    def tailCompileCaseStr(e : Expression, es : Vector[Expression], css : Vector[Case],
        d : Default, k : String) : Term = {

        val grouped = css.groupBy {
            case Case(StrPtrn(str) +: _, _) => str
        }

        val newCases = grouped.map {
            case (cons, cs) => es match {
                case h +: t =>
                    Case(
                        Vector(StrPtrn(cons)),
                        Mat(h, t, cs.map {
                            case Case(StrPtrn(_) +: t, expr) =>
                                Case(t, expr)
                        }, d)
                    )
                case _ => cs(0)
            }
        }

        val dk = fresh("k")

        val cks = newCases.map(c => (c, fresh("k")))

        val caseTerms = cks.map {
            case (Case(StrPtrn(str) +: _, _), k) => strCaseTerm(str, k)
        }.toVector

        compile(e, z => cks.foldLeft(letC(dk, z, d match {
            case Dflt(d)  => tailCompile(d, k)
            case NoDflt() => compileHalt(Num(-1))
        }, casV(z, caseTerms, dk))) {
            case (t, (Case(StrPtrn(str) +: _, ei), ki)) =>
                letC(ki, fresh("v"), tailCompile(ei, k), t)
        })
    }

    def tailCompileMatch(e : Expression, es : Vector[Expression], cs : Vector[Case], d : Default, k : String) : Term = {
        //cases before the split
        val css = cs match {
            case Case(SPtrn(_) +: t, _) +: tail => cs.takeWhile {
                case Case(SPtrn(_) +: t, _) => true
                case _                      => false
            }
            case _ => cs.takeWhile {
                case Case(SPtrn(_) +: t, _) => false
                case _                      => true
            }
        }

        //rest of the cases after the split
        val rest = css match {
            case Case(SPtrn(_) +: t, _) +: tail => cs.dropWhile {
                case Case(SPtrn(_) +: t, _) => true
                case _                      => false
            }
            case _ => cs.dropWhile {
                case Case(SPtrn(_) +: t, _) => false
                case _                      => true
            }
        }

        //default with the rest of the cases
        //(major tree explosion ?)
        val nd = rest match {
            case h +: t => Dflt(Mat(e, es, rest, d))
            case _      => d
        }

        //determining to compile with case2 or case3
        css match {
            case Case(SPtrn(_) +: _, _) +: _ =>
                tailCompileCase_2(e, es, css, nd, k)
            case Case(VPtrn(_, _) +: _, _) +: _ =>
                tailCompileCase_3(e, es, css, nd, k)
            case Case(r @ (RPtrnLit(_, _) | RPtrnCons(_, _, _) | RPtrnE()) +: _, _) +: _ =>
                tailCompileCaseRec(e, es, css, nd, k)
            case Case(IPtrn(_) +: _, _) +: _ =>
                tailCompileCaseInt(e, es, css, nd, k)
            case Case(StrPtrn(_) +: _, _) +: _ =>
                tailCompileCaseStr(e, es, css, nd, k)
        }
    }

}
