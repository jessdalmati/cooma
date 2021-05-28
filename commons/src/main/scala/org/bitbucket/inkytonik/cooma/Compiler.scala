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

            // case Mat(e, cs) =>
            //     compileMatch(e, cs, kappa)

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

    def compileMatchErr() : Term = {
        compileHalt(Num(-1))
    }

    // def compileMatch(e : Expression, cs : Vector[Case], kappa : String => Term) : Term = {
    //     val cks = cs.map(c => (c, fresh("k")))
    //     val caseTerms = cks.map { case (c, k) => caseTerm(c.identifier, k) }
    //     compile(e, z =>
    //         cks.foldLeft(casV(z, caseTerms)) {
    //             case (t, (Case(_, IdnDef(xi), ei), ki)) =>
    //                 letC(ki, xi, compile(ei, zi => kappa(zi)),
    //                     t)
    //         })
    // }

    def getPrefix(cs : Vector[Case]) : Vector[Case] = {
        val lead = cs(0).patterns(0)

        lead match {
            case RecCon(f1, _, _) =>
                cs.takeWhile {
                    case Case(RecCon(f2, flds, _) +: _, _) =>
                        (f2 +: flds).map {
                            case FPtrn(l, _) => l
                            case LPtrn(l)    => l
                        }.contains(f1 match {
                            case FPtrn(l, _) => l
                            case LPtrn(l)    => l
                        })
                    case _ => false
                }
            case RecLit(f1, _) =>
                cs.takeWhile {
                    case Case(RecLit(f2, flds) +: _, _) =>
                        (f2 +: flds).map {
                            case FPtrn(l, _) => l
                            case LPtrn(l)    => l
                        }.contains(f1 match {
                            case FPtrn(l, _) => l
                            case LPtrn(l)    => l
                        })
                    case _ => false
                }
            case SPtrn(_) =>
                cs.takeWhile {
                    case Case(SPtrn(_) +: _, _) => true
                    case _                      => false
                }
            case _ =>
                cs.takeWhile {
                    case Case(SPtrn(_) +: _, _) => false
                    case _                      => true
                }
        }
    }

    def getSuffix(cs : Vector[Case]) : Vector[Case] = {
        val lead = cs(0).patterns(0)

        lead match {
            case RecCon(f1, _, _) =>
                cs.dropWhile {
                    case Case(RecCon(f2, flds, _) +: _, _) =>
                        (f2 +: flds).map {
                            case FPtrn(l, _) => l
                            case LPtrn(l)    => l
                        }.contains(f1 match {
                            case FPtrn(l, _) => l
                            case LPtrn(l)    => l
                        })
                    case _ => false
                }
            case RecLit(f1, _) =>
                cs.dropWhile {
                    case Case(RecLit(f2, flds) +: _, _) =>
                        (f2 +: flds).map {
                            case FPtrn(l, _) => l
                            case LPtrn(l)    => l
                        }.contains(f1 match {
                            case FPtrn(l, _) => l
                            case LPtrn(l)    => l
                        })
                    case _ => false
                }
            case SPtrn(_) =>
                cs.dropWhile {
                    case Case(SPtrn(_) +: _, _) => true
                    case _                      => false
                }
            case _ =>
                cs.dropWhile {
                    case Case(SPtrn(_) +: _, _) => false
                    case _                      => true
                }
        }
    }

    def compileMatch(e : Expression, es : Vector[Expression], cs : Vector[Case], d : Default, kappa : String => Term) : Term = {
        //cases before the split
        val css = getPrefix(cs)

        //rest of the cases after the split
        val rest = getSuffix(cs)

        //default with the rest of the cases
        val nd = rest match {
            case h +: t => Dflt(Mat(e, es, rest, d))
            case _      => d
        }

        css match {
            case Case(SPtrn(_) +: _, _) +: _ =>
                compileMatchCase_2(e, es, css, nd, kappa)
            case Case(VPtrn(_, _) +: _, _) +: _ =>
                compileMatchCase_3(e, es, css, nd, kappa)
            case Case(IntCons(_) +: _, _) +: _ =>
                compileIntCons(e, es, css, nd, kappa)
            case Case(StrCons(_) +: _, _) +: _ =>
                compileStrCons(e, es, css, nd, kappa)
            case Case((RecCon(_, _, _) | RecLit(_, _)) +: _, _) +: _ =>
                compileRecPtrn(e, es, css, nd, kappa)
        }
    }

    def compileRecPtrn(e : Expression, es : Vector[Expression], cs : Vector[Case], d : Default, kappa : String => Term) : Term = {
        //determine if all literals
        val isMixed = cs.exists(c => c match {
            case Case(RecCon(_, _, _) +: _, _) => true
            case _                             => false
        })

        isMixed match {
            case true => //make all concat patterns and compile as per rec mixed case
                val css = cs.map(c => c match {
                    case Case(RecLit(f, fs) +: ptrns, exp) => Case(RecCon(f, fs, IdnDef(fresh("r"))) +: ptrns, exp)
                    case cse                               => cse
                })
                compileCaseRecCon(e, es, css, d, kappa)
            case false => //compile as all lit
                compileCaseRecLit(e, es, cs, d, kappa)
        }
    }

    def compileCaseRecLit(e : Expression, es : Vector[Expression], cs : Vector[Case], d : Default, kappa : String => Term) : Term = {
        val labels = cs(0).patterns(0) match {
            case RecLit(f, fs) => (f +: fs).map {
                case FPtrn(l, _) => l
                case LPtrn(l)    => l
            }
            case _ => Vector()
        }

        val ess = labels.map(l => Sel(e, FieldUse(l))) ++ es

        val css = cs.map {
            case Case(RecLit(f, fs) +: ptrns, expr) =>
                Case((f +: fs).map {
                    case FPtrn(l, sp) => sp
                    case LPtrn(l)     => SPtrn(IdnDef(l))
                } ++ ptrns, labels.foldLeft(expr) {
                    case (exp, l) => substExp(Sel(e, FieldUse(l)), l, exp)
                })
            case c => c
        }

        ess match {
            case e +: es => compileMatch(e, es, css, d, kappa)
            case _       => compileMatchErr()
        }
    }

    def compileCaseRecCon(e : Expression, es : Vector[Expression], cs : Vector[Case], d : Default, kappa : String => Term) : Term = {
        val label = cs(0).patterns(0) match {
            case RecCon(f, _, _) => f match {
                case FPtrn(l, _) => l
                case LPtrn(l)    => l
            }
            case _ => ""
        }

        val ess = Sel(e, FieldUse(label)) +: subtractRec(e, label) +: es

        val css = cs.map {
            case Case(RecCon(f, fs, v) +: ptrns, expr) => {
                val newFields = (f +: fs).filterNot {
                    case FPtrn(`label`, _) => true
                    case LPtrn(`label`)    => true
                    case _                 => false
                }
                val subPtrn = (f +: fs).find {
                    case FPtrn(`label`, _) => true
                    case LPtrn(`label`)    => true
                    case _                 => false
                } match {
                    case Some(fieldPtrn) => fieldPtrn match {
                        case FPtrn(l, sp) => sp
                        case LPtrn(l)     => SPtrn(IdnDef(l))
                    }
                    case None => sys.error(s"label $label not found in record pattern")
                }
                newFields match {
                    case hd +: tl => Case(subPtrn +: RecCon(hd, tl, v) +: ptrns, substExp(Sel(e, FieldUse(label)), label, expr))
                    case _        => Case(Vector(subPtrn, SPtrn(v)), substExp(Sel(e, FieldUse(label)), label, expr))
                }
            }
        }

        ess match {
            case e +: es => compileMatch(e, es, css, d, kappa)
            case _       => compileMatchErr()
        }
    }

    def subtractRec(r : Expression, l : String) : Expression = {
        r match {
            case Rec(fs) =>
                val newFields = fs.filterNot(f => f.identifier == l)
                newFields match {
                    case hd +: tl => Rec(newFields)
                    case _        => Uni()
                }
            case _ => r
        }
    }

    def substExp(e : Expression, idn : String, E : Expression) : Expression = {
        val prog = Program(E)
        val semanticAnalyser = new SemanticAnalyser(new Tree(prog))
        val substIdn =
            rule[ASTNode] {
                case Idn(i @ IdnUse(`idn`)) if semanticAnalyser.entity(i) == UnknownEntity() => e
            }
        rewrite(everywhere(substIdn))(prog) match {
            case Program(e) => e
        }
    }

    def compileIntCons(e : Expression, es : Vector[Expression], cs : Vector[Case], d : Default, kappa : String => Term) : Term = {
        val grouped = cs.groupBy {
            case Case(IntCons(i) +: _, _) => i
        }

        val newCases = grouped.map {
            case (cons, cs) => es match {
                case h +: t =>
                    Case(
                        Vector(IntCons(cons)),
                        Mat(h, t, cs.map {
                            case Case(IntCons(_) +: t, expr) =>
                                Case(t, expr)
                        }, d)
                    )
                case _ => cs(0)
            }
        }

        val dk = fresh("k")

        val cks = newCases.map(c => (c, fresh("k")))

        val caseTerms = cks.map {
            case (Case(IntCons(i) +: _, _), k) => intCaseTerm(i, k)
        }.toVector

        val nd = d match {
            case Dflt(d)  => compile(d, zi => kappa(zi))
            case NoDflt() => compileMatchErr()
        }

        compile(e, z => cks.foldLeft(letC(dk, z, nd, casV(z, caseTerms, dk))) {
            case (t, (Case(IntCons(_) +: _, ei), ki)) =>
                letC(ki, fresh("v"), compile(ei, zi => kappa(zi)), t)
        })
    }

    def compileStrCons(e : Expression, es : Vector[Expression], cs : Vector[Case], d : Default, kappa : String => Term) : Term = {
        val grouped = cs.groupBy {
            case Case(StrCons(s) +: _, _) => s
        }

        val newCases = grouped.map {
            case (cons, cs) => es match {
                case h +: t =>
                    Case(
                        Vector(StrCons(cons)),
                        Mat(h, t, cs.map {
                            case Case(StrCons(_) +: t, expr) =>
                                Case(t, expr)
                        }, d)
                    )
                case _ => cs(0)
            }
        }

        val dk = fresh("k")

        val cks = newCases.map(c => (c, fresh("k")))

        val caseTerms = cks.map {
            case (Case(StrCons(s) +: _, _), k) => strCaseTerm(s, k)
        }.toVector

        val nd = d match {
            case Dflt(d)  => compile(d, zi => kappa(zi))
            case NoDflt() => compileMatchErr()
        }

        compile(e, z => cks.foldLeft(letC(dk, z, nd, casV(z, caseTerms, dk))) {
            case (t, (Case(StrCons(_) +: _, ei), ki)) =>
                letC(ki, fresh("v"), compile(ei, zi => kappa(zi)), t)
        })
    }

    def compileMatchCase_2(e : Expression, es : Vector[Expression], cs : Vector[Case], d : Default, kappa : String => Term) : Term = {
        val dk = fresh("k")
        val vi = fresh("v")

        val cks = es match {
            case h +: t =>
                ((SPtrn(IdnDef(vi)), Mat(h, t, cs.map {
                    case Case(SPtrn(IdnDef(idn)) +: t, ei) =>
                        Case(t, substExp(e, idn, ei))
                }, d)), fresh("k"))
            case _ => cs(0) match {
                case Case(p +: _, ei) =>
                    ((p, ei), fresh("k"))
            }
        }

        val caseTerms = cks match {
            case (_, k) => Vector(sCaseTerm(k))
        }

        compile(e, z =>
            cks match {
                case ((SPtrn(IdnDef(xi)), ei), ki) =>
                    letC(ki, xi, compile(ei, zi => kappa(zi)),
                        letC(dk, z, compileMatchErr(),
                            casV(z, caseTerms, dk)))
            })
    }

    def compileMatchCase_3(e : Expression, es : Vector[Expression], cs : Vector[Case], d : Default, kappa : String => Term) : Term = {
        val grouped = cs.groupBy {
            case Case(VPtrn(cons, _) +: _, _) => cons
        }

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

        val cks = newCases.map(cs => (cs, fresh("k")))

        val caseTerms = cks.map {
            case (Case(VPtrn(idn, _) +: _, _), k) => vCaseTerm(idn, k)
        }.toVector

        val nd = d match {
            case Dflt(d)  => compile(d, zi => kappa(zi))
            case NoDflt() => compileMatchErr()
        }

        compile(e, z => cks.foldLeft(letC(dk, z, nd, casV(z, caseTerms, dk))) {
            case (t, (Case(VPtrn(_, SPtrn(IdnDef(xi))) +: _, ei), ki)) =>
                letC(ki, xi, compile(ei, zi => kappa(zi)), t)
        })
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

    // def tailCompileMatch(e : Expression, cs : Vector[Case], k : String) : Term = {
    //     val cks = cs.map(c => (c, fresh("k")))
    //     val caseTerms = cks.map { case (c, k) => caseTerm(c.identifier, k) }
    //     compile(e, z =>
    //         cks.foldLeft(casV(z, caseTerms)) {
    //             case (t, (Case(vi, IdnDef(xi), ei), ki)) =>
    //                 letC(ki, xi, tailCompile(ei, k),
    //                     t)
    //         })
    // }

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
        val nd = rest match {
            case h +: t => Dflt(Mat(e, es, rest, d))
            case _      => d
        }

        css match {
            case Case(SPtrn(_) +: _, _) +: _    => tailCompileMatchCase_2(e, es, css, nd, k)
            case Case(VPtrn(_, _) +: _, _) +: _ => tailCompileMatchCase_3(e, es, css, nd, k)
            case Case(IntCons(_) +: _, _) +: _  => tailCompileIntCons(e, es, css, nd, k)
            case Case(StrCons(_) +: _, _) +: _  => tailCompileStrCons(e, es, css, nd, k)
        }
    }

    def tailCompileIntCons(e : Expression, es : Vector[Expression], cs : Vector[Case], d : Default, k : String) : Term = {
        val grouped = cs.groupBy {
            case Case(IntCons(i) +: _, _) => i
        }

        val newCases = grouped.map {
            case (cons, cs) => es match {
                case h +: t =>
                    Case(
                        Vector(IntCons(cons)),
                        Mat(h, t, cs.map {
                            case Case(IntCons(_) +: t, expr) =>
                                Case(t, expr)
                        }, d)
                    )
                case _ => cs(0)
            }
        }

        val dk = fresh("k")

        val cks = newCases.map(c => (c, fresh("k")))

        val caseTerms = cks.map {
            case (Case(IntCons(i) +: _, _), k) => intCaseTerm(i, k)
        }.toVector

        val nd = d match {
            case Dflt(d)  => tailCompile(d, k)
            case NoDflt() => compileMatchErr()
        }

        compile(e, z => cks.foldLeft(letC(dk, z, nd, casV(z, caseTerms, dk))) {
            case (t, (Case(IntCons(_) +: _, ei), ki)) =>
                letC(ki, fresh("v"), tailCompile(ei, k), t)
        })
    }

    def tailCompileStrCons(e : Expression, es : Vector[Expression], cs : Vector[Case], d : Default, k : String) : Term = {
        val grouped = cs.groupBy {
            case Case(StrCons(s) +: _, _) => s
        }

        val newCases = grouped.map {
            case (cons, cs) => es match {
                case h +: t =>
                    Case(
                        Vector(StrCons(cons)),
                        Mat(h, t, cs.map {
                            case Case(StrCons(_) +: t, expr) =>
                                Case(t, expr)
                        }, d)
                    )
                case _ => cs(0)
            }
        }

        val dk = fresh("k")

        val cks = newCases.map(c => (c, fresh("k")))

        val caseTerms = cks.map {
            case (Case(StrCons(s) +: _, _), k) => strCaseTerm(s, k)
        }.toVector

        val nd = d match {
            case Dflt(d)  => tailCompile(d, k)
            case NoDflt() => compileMatchErr()
        }

        compile(e, z => cks.foldLeft(letC(dk, z, nd, casV(z, caseTerms, dk))) {
            case (t, (Case(StrCons(_) +: _, ei), ki)) =>
                letC(ki, fresh("v"), tailCompile(ei, k), t)
        })
    }

    def tailCompileMatchCase_2(e : Expression, es : Vector[Expression], cs : Vector[Case], d : Default, k : String) : Term = {
        val dk = fresh("k")
        val vi = fresh("v")

        val cks = es match {
            case h +: t =>
                ((SPtrn(IdnDef(vi)), Mat(h, t, cs.map {
                    case Case(SPtrn(IdnDef(idn)) +: t, ei) =>
                        Case(t, substExp(e, idn, ei))
                }, d)), fresh("k"))
            case _ => cs(0) match {
                case Case(p +: _, ei) =>
                    ((p, ei), fresh("k"))
            }
        }

        val caseTerms = cks match {
            case (_, k) => Vector(sCaseTerm(k))
        }

        compile(e, z =>
            cks match {
                case ((SPtrn(IdnDef(xi)), ei), ki) =>
                    letC(ki, xi, tailCompile(ei, k),
                        letC(dk, z, compileMatchErr(),
                            casV(z, caseTerms, dk)))
            })
    }

    def tailCompileMatchCase_3(e : Expression, es : Vector[Expression], cs : Vector[Case], d : Default, k : String) : Term = {
        val grouped = cs.groupBy {
            case Case(VPtrn(cons, _) +: _, _) => cons
        }

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

        val cks = newCases.map(cs => (cs, fresh("k")))

        val caseTerms = cks.map {
            case (Case(VPtrn(idn, _) +: _, _), k) => vCaseTerm(idn, k)
        }.toVector

        val nd = d match {
            case Dflt(d)  => tailCompile(d, k)
            case NoDflt() => compileMatchErr()
        }

        compile(e, z => cks.foldLeft(letC(dk, z, nd, casV(z, caseTerms, dk))) {
            case (t, (Case(VPtrn(_, SPtrn(IdnDef(xi))) +: _, ei), ki)) =>
                letC(ki, xi, tailCompile(ei, k), t)
        })
    }

}
