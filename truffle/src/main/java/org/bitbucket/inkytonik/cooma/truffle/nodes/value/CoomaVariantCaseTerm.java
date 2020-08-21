package org.bitbucket.inkytonik.cooma.truffle.nodes.value;

import com.oracle.truffle.api.nodes.NodeInfo;
import lombok.Getter;
import org.bitbucket.inkytonik.cooma.truffle.nodes.CoomaNode;

@Getter
@NodeInfo(shortName = "vCaseTerm", description = "A single variant case in casV")
public class CoomaVariantCaseTerm extends CoomaCaseTerm {

    private final String c;

    public CoomaVariantCaseTerm(String c, String k) {
    	super(k);
        this.c = c;
    }

}
