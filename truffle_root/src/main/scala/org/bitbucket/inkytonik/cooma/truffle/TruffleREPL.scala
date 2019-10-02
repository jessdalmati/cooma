package org.bitbucket.inkytonik.cooma.truffle

import org.bitbucket.inkytonik.cooma.{Backend, Compiler, Config, CoomaConstants, REPL}

trait TruffleREPL extends REPL {

    self : Compiler with TruffleBackend =>

    import org.bitbucket.inkytonik.cooma.Config
    import org.bitbucket.inkytonik.cooma.CoomaParserPrettyPrinter.format
    import org.bitbucket.inkytonik.cooma.CoomaParserSyntax.{Expression, Program}
    import org.graalvm.polyglot.Context

    var currentDynamicEnv : Context = _

    override def initialise() {
        super.initialise()
        currentDynamicEnv = Context.newBuilder(CoomaConstants.ID).build()
    }

    def process(
        program : Program,
        i : String,
        tipe : Expression,
        config : Config
    ) {
        execute(i, tipe, config, {
            val line = format(program).layout
            val result = currentDynamicEnv.eval(CoomaConstants.ID, line)
            output(i, tipe, Some(result), config)
        })
    }

}

object TruffleReplFrontendHolder {
    def repl(config : Config) : REPL with Compiler with Backend =
        new TruffleBackend(config) with TruffleREPL with Compiler
}
