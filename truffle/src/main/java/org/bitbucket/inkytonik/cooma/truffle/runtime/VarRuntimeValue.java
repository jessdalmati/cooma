package org.bitbucket.inkytonik.cooma.truffle.runtime;

import com.oracle.truffle.api.interop.TruffleObject;
import de.uka.ilkd.pp.DataLayouter;
import java.util.Comparator;
import lombok.EqualsAndHashCode;
import lombok.Value;
import lombok.val;

@Value
@EqualsAndHashCode(callSuper=false)
public class VarRuntimeValue extends RuntimeValue implements TruffleObject, Comparable<VarRuntimeValue>{

    private final String c;
    private final RuntimeValue v;

    public VarRuntimeValue(String c, RuntimeValue v) {
        this.c = c;
        this.v = v;
    }

    @Override
    public int compareTo(VarRuntimeValue varRuntimeValue) {
        return Comparator.comparing(VarRuntimeValue::getC).compare(this, varRuntimeValue);
    }


    @Override
    public String toString() {
        val vp = v.print();
        if (vp.equals("{}"))
            return c.toLowerCase();
        else
            return String.format("< %s = %s >", c, v.print());
    }

    @Override
    public <Exc extends java.lang.Exception> void prettyPrint(DataLayouter<Exc> l) throws Exc {
        l.print(this.toString());
    }

}
