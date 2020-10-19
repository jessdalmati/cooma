package org.bitbucket.inkytonik.cooma

import org.bitbucket.inkytonik.kiama.util.Tests
import org.bitbucket.inkytonik.kiama.util.TestCompilerWithConfig
import org.bitbucket.inkytonik.cooma.CoomaParserSyntax.{ASTNode, Program}

class PatternTests extends Driver with Tests with TestCompilerWithConfig[ASTNode, Program, Config] {

    import org.bitbucket.inkytonik.cooma.backend.ReferenceBackend
    import org.bitbucket.inkytonik.kiama.util.{Source, StringSource}
    import org.rogach.scallop.throwError

    case class Backend(
        name : String,
        options : Seq[String],
        frontend : Frontend
    )

    case class FileTest(
        file : String,
        name : String,
        expected : String,
        args : Seq[String]
    )

    case class WriteTest(
        file : String,
        name : String,
        expected : String,
        writer : String,
        args : Seq[String]
    )

    case class ReadTest(
        file : String,
        name : String,
        expected : String,
        reader : String,
        args : Seq[String]
    )

    case class ReadWriteTest(
        file : String,
        name : String,
        expected : String,
        reader : String,
        writer : String,
        args : Seq[String]
    )

    val backend = Backend("Reference", Seq(), new ReferenceFrontend)

    val testFiles = Vector(
        FileTest(
            "src/test/resources/patterns/nestedPersonVariant.cooma",
            "Nested variant patterns 1",
            "true\n",
            Seq("-r")
        ),
        FileTest(
            "src/test/resources/patterns/nestedEventVariant.cooma",
            "Nested variant patterns 2",
            "\"move left\"\n",
            Seq("-r")
        )
    )

    for (tf <- testFiles) {
        test(tf.name) {
            val result = runFile(tf.file, Seq("-r") ++ backend.options, backend, Seq())
            result shouldBe tf.expected
        }
    }

    def runFile(program : String, options : Seq[String], backend : Backend, args : Seq[String]) : String = {
        val allArgs = Seq("--Koutput", "string") ++ options ++ (program +: args)
        runTest(backend.frontend.interpret, options, allArgs)
    }

    def runTest(tester : Config => Unit, options : Seq[String], args : Seq[String]) : String = {
        val config = makeConfig(args)
        try {
            tester(config)
        } catch {
            case e : Exception =>
                info("failed with an exception ")
                throw (e)
        }
        config.stringEmitter.result
    }

    def makeConfig(args : Seq[String]) : Config = {
        // Set Scallop so that errors don't just exit the process
        val saveThrowError = throwError.value
        throwError.value = true
        val config = createConfig(args)
        config.verify()
        throwError.value = saveThrowError
        config
    }

    override def createREPL(config : Config) : REPL with Compiler with org.bitbucket.inkytonik.cooma.Backend = {
        val repl = {
            val source = new StringSource("")
            new ReferenceBackend(this, source, config) with ReferenceREPL with Compiler
        }

        repl.initialise()
        repl
    }

    override def process(source : Source, prog : Program, config : Config) : Unit = {
        val frontend = new ReferenceDriver
        frontend.process(source, prog, config)
    }

}