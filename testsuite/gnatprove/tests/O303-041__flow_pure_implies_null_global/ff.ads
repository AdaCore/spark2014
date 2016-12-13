with Ada.Numerics.Generic_Elementary_Functions;

package FF is new Ada.Numerics.Generic_Elementary_Functions (Float);
--  The generic unit Ada.Numerics.Generic_Elementary_Functions has pragma
--  Pure, but this pragma applies only to the generic itself, not to the
--  instance. In effect, flow analysis is still expected to warn that it is
--  assuming Global => null on subprograms from this instance.
