package org.bitbucket.inkytonik.cooma

import org.scalatest.{FunSuiteLike, Matchers}

class Tests extends FunSuiteLike with Matchers {

    import java.nio.file.{Files, Paths}
    import org.bitbucket.inkytonik.kiama.util.Filenames.makeTempFilename
    import org.bitbucket.inkytonik.kiama.util.FileSource
    import org.bitbucket.inkytonik.kiama.util.IO.{createFile, deleteFile}
    import org.rogach.scallop.throwError

    case class Test(
        name : String,
        program : String,
        expectedResult : String,
        args : Seq[String] = Seq()
    )

    val tests =
        List(
            // Functional core

            Test("integer",
                 "42",
                 "42"),
            Test("string",
                 """"hello"""",
                 """"hello""""),
            Test("string with quote",
                 """"hel\"lo"""",
                 """"hel\"lo""""),
            Test("string with newline",
                 """"hello\n"""",
                 """"hello\n""""),
            Test("row",
                 "{x = 65}",
                 "{x = 65}"),
            Test("field select",
                 """{s = "Hi"}.s""",
                 """"Hi""""),
            Test("nested field select",
                 "{r = {y = 42}}.r.y",
                 "42"),
            Test("unit",
                 "{}",
                 "{}"),
            Test("unit argument",
                 "(fun (x : {}) => 100)()",
                 "100"),
            Test("single integer argument",
                 """(fun (x : Int) => x)(10)""",
                 "10"),
            Test("multiple arguments - first",
                 """(fun (x : Int, y : String) => x)(10, "hello")""",
                 "10"),
            Test("multiple arguments - second",
                 """(fun (x : Int, y : String) => y)(10, "hello")""",
                 """"hello""""),
            Test("row argument",
                 "(fun (r : {x : Int}) => r.x)({x = 20})",
                 "20"),
            Test("single field row return",
                 "(fun (x : Int) => {a = x})(9)",
                 "{a = 9}"),
            Test("function argument",
                 """(fun (f : Int => String) => f(10))(fun (x : Int) => "yes")""",
                 """"yes""""),
            Test("function return then call",
                 "(fun (x : Int) => (fun (y : Int) => x))(10)(15)",
                 "10"),
            Test("function program result",
                 "(fun (f : Int => Int) => f)(fun (x : Int) => x)",
                 "<function>"),

            // Command-line arguments

            Test("string command argument",
                 "fun (s : String) => s",
                 """"hello"""",
                 Seq("hello")),
            Test("multiple string command arguments",
                 "fun (s : String, t : String) => t",
                 """"there"""",
                 Seq("hello", "there"))
        )

    for (aTest <- tests) {
        test(aTest.name) {
            val result = runCooma(aTest.name, aTest.program, Seq(), aTest.args)
            result shouldBe ""
        }
        test(s"${aTest.name}: result") {
            val result = runCooma(aTest.name, aTest.program, Seq("-r"), aTest.args)
            result shouldBe s"${aTest.expectedResult}\n"
        }
    }

    {
        val name = "console command argument"
        val program = """fun (c : Console) => c.write("Hello world!\n")"""
        val console = makeTempFilename(".txt")
        val args = Seq(console)
        val content = "Hello world!\n"

        test(s"$name") {
            createFile(console, "")
            val result = runCooma(name, program, Seq(), args)
            result shouldBe ""
            FileSource(console).content shouldBe content
            deleteFile(console)
        }

        test(s"$name: result") {
            createFile(console, "")
            val result = runCooma(name, program, Seq("-r"), args)
            result shouldBe "{}\n"
            FileSource(console).content shouldBe content
            deleteFile(console)
        }

        test(s"$name: non-existent console") {
            val filename = "notThere.txt"
            val result = runCooma(name, program, Seq(), Seq(filename))
            result shouldBe "cooma: Console capability unavailable: can't write notThere.txt\n"
            Files.exists(Paths.get(filename)) shouldBe false
        }
    }

    {
        val name = "console and reader command arguments"
        val program = "fun (c : Console, r : Reader) => c.write(r.read())"
        val console = makeTempFilename(".txt")
        val reader = makeTempFilename(".txt")
        val args = Seq(console, reader)
        val content = "The file contents"

        test(s"$name") {
            createFile(console, "")
            createFile(reader, content)
            val result = runCooma(name, program, Seq(), args)
            result shouldBe ""
            FileSource(console).content shouldBe content
            FileSource(reader).content shouldBe content
            deleteFile(console)
            deleteFile(reader)
        }

        test(s"$name: result") {
            createFile(console, "")
            createFile(reader, content)
            val result = runCooma(name, program, Seq("-r"), args)
            result shouldBe "{}\n"
            FileSource(console).content shouldBe content
            FileSource(reader).content shouldBe content
            deleteFile(console)
            deleteFile(reader)
        }

        test(s"$name: non-existent console") {
            createFile(reader, "")
            val filename = "notThere.txt"
            val result = runCooma(name, program, Seq(), Seq(filename, reader))
            result shouldBe s"cooma: Console capability unavailable: can't write $filename\n"
            Files.exists(Paths.get(filename)) shouldBe false
            deleteFile(console)
        }

        test(s"$name: non-existent reader") {
            createFile(console, "")
            val filename = "notThere.txt"
            val result = runCooma(name, program, Seq(), Seq(console, filename))
            result shouldBe s"cooma: Reader capability unavailable: can't read $filename\n"
            Files.exists(Paths.get(filename)) shouldBe false
            deleteFile(console)
        }
    }

    def runCooma(name : String, program : String, options : Seq[String], args : Seq[String]) : String = {
        val allArgs = Seq("--Koutput", "string") ++ options ++ ("test.cooma" +: args)

        // Set Scallop so that errors don't just exit the process
        val saveThrowError = throwError.value
        throwError.value = true
        val config = Main.createConfig(allArgs)
        config.verify()
        throwError.value = saveThrowError

        try {
            Main.compileString(name, program, config)
        } catch {
            case e : Exception =>
                info("failed with an exception ")
                throw (e)
        }
        config.stringEmitter.result
    }

}