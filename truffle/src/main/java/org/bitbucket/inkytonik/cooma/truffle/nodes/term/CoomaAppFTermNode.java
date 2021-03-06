package org.bitbucket.inkytonik.cooma.truffle.nodes.term;

import com.oracle.truffle.api.dsl.Specialization;
import com.oracle.truffle.api.frame.VirtualFrame;
import com.oracle.truffle.api.nodes.NodeInfo;
import org.bitbucket.inkytonik.cooma.CoomaConstants;
import org.bitbucket.inkytonik.cooma.truffle.exceptions.CoomaException;
import org.bitbucket.inkytonik.cooma.truffle.nodes.environment.Rho;
import org.bitbucket.inkytonik.cooma.truffle.runtime.*;

@NodeInfo(shortName = "appF", description = "Function application")
public abstract class CoomaAppFTermNode extends CoomaTermNode {

    /**
     * Function identifier
     */
    private final String f;

    /**
     * Continuation identifier
     */
    private final String k;

    /**
     * Parameter identifier
     */
    private final String x;


    public CoomaAppFTermNode(String identifier, String k, String x) {
        this.f = identifier;
        this.k = k;
        this.x = x;
    }

    @Specialization(guards = "isHalt()")
    Object executeHalt(VirtualFrame frame) {
        FunctionClosureHolder value = (FunctionClosureHolder) obtainFromRho(f);
        FunctionClosure closure = value.get(f);
        Rho p1 = closure.getRho()
                .extend(closure.getK(),
                        new ContinuationClosure(obtainRho(),
                                this.x, CoomaAppCTermNodeGen.create(CoomaConstants.HALT, this.x)))
                .extend(closure.getX(), obtainFromRho(this.x));
        replaceRho(p1);
        return closure.getZ().executeGeneric(frame);
    }

    @Specialization
    Object execute(VirtualFrame frame) {

        RuntimeValue value = obtainFromRho(f);
        if (value instanceof FunctionClosureHolder) {
            FunctionClosure closure = ((FunctionClosureHolder) value).get(f);
            Rho p1 = closure.getRho()
                    .extend(closure.getK(), obtainFromRho(this.k))
                    .extend(closure.getX(), obtainFromRho(this.x));
            replaceRho(p1);
            if (closure.getZ().getParent() == null){
                this.insert(closure.getZ());
            }
            return closure.getZ().executeGeneric(frame);

        } else if (value instanceof ErrorRuntimeValue) {
            return value;
        } else {
            throw new CoomaException(String.format("interpret AppF: %s is %s", f, value.print()), this);
        }
    }

    boolean isHalt() {
        return CoomaConstants.HALT.equals(this.k);
    }
}
