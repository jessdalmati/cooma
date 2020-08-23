package org.bitbucket.inkytonik.cooma.truffle.nodes.term;

import com.oracle.truffle.api.frame.VirtualFrame;
import com.oracle.truffle.api.nodes.NodeInfo;
import org.bitbucket.inkytonik.cooma.truffle.exceptions.CoomaException;
import org.bitbucket.inkytonik.cooma.truffle.nodes.environment.Rho;
import org.bitbucket.inkytonik.cooma.truffle.nodes.value.CoomaCaseTerm;
import org.bitbucket.inkytonik.cooma.truffle.nodes.value.CoomaVariantCaseTerm;
import org.bitbucket.inkytonik.cooma.truffle.nodes.value.CoomaDefaultCaseTerm;
import org.bitbucket.inkytonik.cooma.truffle.runtime.ContinuationClosure;
import org.bitbucket.inkytonik.cooma.truffle.runtime.RuntimeValue;
import org.bitbucket.inkytonik.cooma.truffle.runtime.VarRuntimeValue;

@NodeInfo(shortName = "casV", description = "Multi-way case branching")
public class CoomaCasVTermNode extends CoomaTermNode {

    private final String x;
    private final CoomaVariantCaseTerm[] vcs;
    private final CoomaDefaultCaseTerm dcs;

    public CoomaCasVTermNode(String x, CoomaVariantCaseTerm[] vcs, CoomaDefaultCaseTerm dcs) {
        this.x = x;
        this.vcs = vcs;
        this.dcs = dcs;
    }

    @Override
    public Object executeGeneric(VirtualFrame frame) {
        RuntimeValue value = obtainFromRho(x);
        if (value instanceof VarRuntimeValue) {
            VarRuntimeValue var = (VarRuntimeValue) value;
            String c1 = var.getC();
            for (CoomaVariantCaseTerm kase : vcs) {
                if (c1.equals(kase.getC())) {
                    String k = kase.getK();
                    RuntimeValue cont = obtainFromRho(k);
                    if (cont instanceof ContinuationClosure) {
                        ContinuationClosure closure = (ContinuationClosure) cont;
                        Rho p1 = closure.getRho()
                                .extend(closure.getX(), var.getV());
                        replaceRho(p1);
                        return closure.getZ().executeGeneric(frame);
                    } else {
                        throw new CoomaException(String.format("interpret CasV: %s is %s", k, cont.print()), this);
                    }
                }
            }
            if(!dcs.equals(null)) {
                String k = dcs.getK();
                RuntimeValue cont = obtainFromRho(k);
                if (cont instanceof ContinuationClosure) {
                    ContinuationClosure closure = (ContinuationClosure) cont;
                    Rho p1 = closure.getRho()
                            .extend(closure.getX(), var.getV());
                    replaceRho(p1);
                    return closure.getZ().executeGeneric(frame);
                } else {
                    throw new CoomaException(String.format("interpret CasV: %s is %s", k, cont.print()), this);
                }
            } else {
                throw new CoomaException(String.format("interpret CasV: can't find case for variant %s", c1), this);
            }
        } else {
            throw new CoomaException(String.format("interpret CasV: %s is %s", x, value.print()), this);
        }
    }
}
