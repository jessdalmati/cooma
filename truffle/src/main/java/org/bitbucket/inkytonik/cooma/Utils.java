package org.bitbucket.inkytonik.cooma;

import org.bitbucket.inkytonik.cooma.truffle.nodes.environment.Rho;
import org.bitbucket.inkytonik.cooma.truffle.runtime.CoomaContext;
import org.bitbucket.inkytonik.cooma.truffle.runtime.RuntimeValue;

public class Utils {

    @SuppressWarnings("unchecked")
    public static RuntimeValue obtainFromRho(CoomaContext coomaContext, String key) {
        return coomaContext.getRho().get(key);
    }

    public static void extendRho(CoomaContext context, String key, RuntimeValue value) {
        replaceRho(context, context.getRho().extend(key, value));
    }

    public static void replaceRho(CoomaContext context, Rho newRho) {
        context.setRho(newRho);
    }


}
