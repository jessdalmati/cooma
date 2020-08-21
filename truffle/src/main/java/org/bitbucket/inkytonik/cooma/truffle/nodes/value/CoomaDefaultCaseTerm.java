package org.bitbucket.inkytonik.cooma.truffle.nodes.value;

import com.oracle.truffle.api.nodes.NodeInfo;
import lombok.Getter;
import org.bitbucket.inkytonik.cooma.truffle.nodes.CoomaNode;

@Getter
@NodeInfo(shortName = "dCaseTerm", description = "A single default case in casV")
public class CoomaDefaultCaseTerm extends CoomaCaseTerm {

    public CoomaDefaultCaseTerm(String k) {
        super(k);
    }

}